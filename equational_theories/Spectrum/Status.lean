import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Evidence attached to Lean declarations

`spectrum_pending theorem proofAvailable "source" "missing formalization"` records
an available argument / reported ATP result whose proof is not integrated into
the default catalogue. An optional completed Lean proof can also await integration;
the source and missing-step fields must say so explicitly. It does **not** claim
we possess an ATP certificate when the note merely
reports a run. `noteGap` instead means that the missing mathematical step itself
has not been reconstructed from the note. Neither category is a completed proof.

`spectrum_assert theorem complete|proofAvailable|noteGap` checks the actual
transitive dependencies. All uses of `sorry` must end at documented pending
declarations; arbitrary axioms are rejected. Native-computation axioms are
allowed only below declarations explicitly tagged `@[spectrum_native]`.

Open mathematical problems have no asserted exact theorem; see the typed
`openProblems` list in `Catalogue.lean`. They are not pending proofs.
-/

open Lean Elab Command
namespace Spectrum.Status

inductive Evidence where
  | complete
  | proofAvailable
  | noteGap
  | mathematicallyOpen
  | sourceConflict
  deriving BEq, Repr, Inhabited

structure PendingInfo where
  evidence : Evidence
  source : String
  missing : String
  deriving Inhabited

/-- An open question or a conflicting source claim, not a theorem with `sorry`. -/
structure OpenIssue where
  equation : Nat
  evidence : Evidence
  description : String
  deriving Repr

initialize pendingExtension : SimplePersistentEnvExtension (Name × PendingInfo)
    (NameMap PendingInfo) ← registerSimplePersistentEnvExtension {
  name := `Spectrum.Status.pendingExtension
  addEntryFn := fun s (n, info) => s.insert n info
  addImportedFn := fun arrays => Id.run do
    let mut s := {}
    for entries in arrays do
      for (n, info) in entries do s := s.insert n info
    return s
}

initialize nativeAttribute : TagAttribute ←
  registerTagAttribute `spectrum_native "Permit native_decide/bv_decide axioms owned by this declaration."

structure Summary where
  pending : Array Name := #[]
  native : Array Name := #[]
  bad : Array Name := #[]
  deriving Inhabited

private def union (a b : Array Name) : Array Name :=
  b.foldl (fun s n => if s.contains n then s else s.push n) a

private def Summary.merge (a b : Summary) : Summary :=
  ⟨union a.pending b.pending, union a.native b.native, union a.bad b.bad⟩

/-- Recognize only tactic-generated axioms owned by an explicitly opted-in theorem. -/
def allowedNativeAxiom (env : Environment) (n : Name) : Bool := Id.run do
  let parts := n.toString.splitOn "._native."
  if parts.length != 2 then return false
  let owner := parts[0]!.toName
  let suffix := parts[1]!
  return nativeAttribute.hasTag env owner &&
    (suffix.startsWith "native_decide.ax_" || suffix.startsWith "bv_decide.ax_")

abbrev AuditM := ReaderT Environment (StateM (NameMap Summary))

/-- Memoized dependency walk. A documented gap is a boundary, not an ignored axiom. -/
partial def analyse (n : Name) : AuditM Summary := do
  if let some s := (← get).find? n then return s
  modify (·.insert n {}) -- break inductive-definition cycles
  let env ← read
  let result ← if (pendingExtension.getState env).contains n then
    pure { pending := #[n] }
  else
    match env.checked.get.find? n with
    | none => pure { bad := #[n] }
    | some ci =>
      match ci with
      | .axiomInfo _ =>
        if n ∈ [``propext, ``Classical.choice, ``Quot.sound] then pure {}
        else if allowedNativeAxiom env n then pure { native := #[n] }
        else pure { bad := #[n] }
      | _ =>
        let deps := ci.type.getUsedConstants ++
          (ci.value?.map Expr.getUsedConstants).getD #[]
        let deps := match ci with
          | .inductInfo v => deps ++ v.ctors.toArray
          | _ => deps
        let mut result := {}
        for d in deps do result := result.merge (← analyse d)
        pure result
  modify (·.insert n result)
  return result

def Summary.evidence (env : Environment) (s : Summary) : Evidence :=
  if s.pending.any (fun n =>
      ((pendingExtension.getState env).find? n).any (·.evidence == .noteGap)) then .noteGap
  else if s.pending.isEmpty then .complete else .proofAvailable

-- Theorems are immutable; clear the cache whenever provenance annotations change.
initialize auditCache : IO.Ref (NameMap Summary) ← IO.mkRef {}

def audit (n : Name) : CommandElabM Summary := do
  let (s, cache) := ((analyse n).run (← getEnv)).run (← auditCache.get)
  auditCache.set cache
  unless s.bad.isEmpty do throwError "{n}: undocumented axioms/dependencies {s.bad}"
  return s

private def parseEvidence (id : Syntax) : CommandElabM Evidence :=
  match id.getId with
  | `complete => pure .complete
  | `proofAvailable => pure .proofAvailable
  | `noteGap => pure .noteGap
  | _ => throwErrorAt id "Expected complete, proofAvailable, or noteGap"

syntax "spectrum_pending " ident ident str str : command
elab_rules : command
  | `(spectrum_pending $decl:ident $kind:ident $source:str $missing:str) => do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo decl)
    let kind ← parseEvidence kind
    if kind == .complete then throwError "A pending declaration cannot be complete"
    let axioms ← Lean.collectAxioms n
    unless axioms.contains ``sorryAx do throwError "{n} has no proof gap; remove its pending annotation"
    for ax in axioms do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx] ||
          allowedNativeAxiom (← getEnv) ax do
        throwError "Unapproved axiom {ax} in pending declaration {n}"
    let info := PendingInfo.mk kind source.getString missing.getString
    modifyEnv (pendingExtension.addEntry · (n, info))
    auditCache.set {}

syntax "spectrum_assert " ident ident : command
elab_rules : command
  | `(spectrum_assert $decl:ident $kind:ident) => do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo decl)
    let expected ← parseEvidence kind
    let s ← audit n
    let actual := s.evidence (← getEnv)
    unless actual == expected do
      throwError "{n}: expected {repr expected}, found {repr actual}; pending={s.pending}"

syntax "#spectrum_status " ident : command
elab_rules : command
  | `(#spectrum_status $decl:ident) => do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo decl)
    let s ← audit n
    logInfo m!"{n}: {repr (s.evidence (← getEnv))}; native checks: {s.native.size}"
    for p in s.pending do
      let some info := (pendingExtension.getState (← getEnv)).find? p | unreachable!
      logInfo m!"{p}: {repr info.evidence}\n  {info.source}\n  {info.missing}"

end Spectrum.Status
