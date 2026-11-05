import equational_theories.Parastrophes.Consequences
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
`@[parastrophe_result]` registers a completed theorem of one of the public question
predicates. Metadata is extracted from its *type*, never from its name. The
attribute rejects conditional theorems, arbitrary axioms and `sorry`.

`@[parastrophe_claim]` records the same precisely typed question as conjectural;
a docstring explaining the available argument is required. It never creates a
proved cell. Unanswered questions need no placeholder theorem or attribute.
-/
namespace Parastrophes
open Lean Meta Law

structure Entry where
  name : String
  file : String
  line : Nat
  equation : Nat
  scope : String
  kind : String
  side : Option String := none
  positive : Bool
  status : String
  targetEquation : Option Nat := none
  targetLaw : Option NatMagmaLaw := none
  term : Option (FreeMagma Nat) := none
  description : String := ""
  deriving ToJson

initialize results : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `Parastrophes.results
    addImportedFn := Array.flatMap id
    addEntryFn := Array.push
  }

/-- A kernel-checked consequence, with all source theorems and conversion rules.
`fineSpectrum` is symmetric; the structural records are directed source → target. -/
structure Consequence where
  name : String
  source : Nat
  target : Nat
  scope : String
  side : String
  kind : String
  refs : Array String
  deriving ToJson

initialize consequences : SimplePersistentEnvExtension Consequence (Array Consequence) ←
  registerSimplePersistentEnvExtension {
    name := `Parastrophes.consequences
    addImportedFn := Array.flatMap id
    addEntryFn := Array.push
  }

private def equationId? (e : Expr) : Option Nat := do
  let name ← e.constName?
  let s := name.toString
  if !s.startsWith "Law" then none else (s.drop 3).toString.toNat?

private def parse (decl : Name) (file : String) (line : Nat) (claim : Bool) : MetaM Entry := do
  let .thmInfo info ← getConstInfo decl | throwError "Parastrophe attributes require a theorem"
  let mut body := info.type
  let mut positive := true
  if body.isAppOfArity ``Not 1 then
    positive := false
    body := body.getAppArgs[0]!
  let args := body.getAppArgs
  let name := body.getAppFn.constName?.getD .anonymous
  let (kind, arity) ← match name with
    | ``QuasigroupLaw => pure ("quasigroup", 2)
    | ``SideQuasigroupLaw => pure ("sideQuasigroup", 3)
    | ``SingleEquation => pure ("singleEquation", 3)
    | ``Characterizes => pure ("singleEquation", 4)
    | ``TermRecovery => pure ("term", 3)
    | ``UniformTermRecovery => pure ("uniformTerm", 3)
    | ``UniformTermWitness => pure ("uniformTerm", 4)
    | _ => throwError "Expected QuasigroupLaw, SideQuasigroupLaw, SingleEquation, Characterizes, TermRecovery, UniformTermRecovery, or UniformTermWitness (or a negation of a question)"
  unless args.size == arity do throwError "Unexpected question arguments"
  if !positive && (name == ``Characterizes || name == ``UniformTermWitness) then
    throwError "Refuting one target equation or one term does not refute existence; negate SingleEquation or UniformTermRecovery instead"
  let some equation := equationId? args[1]! | throwError "Use a catalogue law constant, e.g. Law543, as the source"
  unless 1 ≤ equation && equation ≤ 4694 do throwError "Source equation outside the catalogue"
  let scopeExpr ← whnf args[0]!
  let scope ← if scopeExpr.isConstOf ``Scope.all then pure "all"
    else if scopeExpr.isConstOf ``Scope.fin then pure "fin"
    else throwError "Expected scope .all or .fin"
  let side ← if arity > 2 then do
      let sideExpr ← whnf args[2]!
      if sideExpr.isConstOf ``Side.left then pure (some "left")
      else if sideExpr.isConstOf ``Side.right then pure (some "right")
      else throwError "Expected division side .left or .right"
    else pure none
  let targetLaw ← if name == ``Characterizes then
      pure (some (← unsafe evalExpr NatMagmaLaw (mkConst ``NatMagmaLaw) args[3]!))
    else pure none
  let term ← if name == ``UniformTermWitness then do
      let t ← unsafe evalExpr (FreeMagma (Fin 2)) (← inferType args[3]!) args[3]!
      pure (some (FreeMagma.fmapFreeMagma Fin.val t))
    else pure none
  let description := (← findDocString? (← getEnv) decl).getD ""
  if claim && description.isEmpty then throwError "A parastrophe claim needs a docstring explaining the purported proof"
  let axioms ← Lean.collectAxioms decl
  for ax in axioms do
    unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] || (claim && ax == ``sorryAx) do
      throwError "Parastrophe evidence uses an unapproved axiom: {ax}"
  return {
    name := decl.toString
    file := file
    line := line
    equation := equation
    scope := scope
    kind := kind
    side := side
    positive := positive
    status := if claim then "PROOF_AVAILABLE" else "PROVED"
    targetEquation := if name == ``Characterizes then equationId? args[3]! else none
    targetLaw := targetLaw
    term := term
    description := description
  }

private def sideProof? (entries : Array Entry) (equation : Nat) (scope side : String) :
    MetaM (Option Expr) := do
  for e in entries do
    if !e.positive || e.status != "PROVED" || (scope == "all" && e.scope != "all") then continue
    let isTarget := e.kind == "singleEquation" && e.targetEquation == some equation
    if !isTarget && e.equation != equation then continue
    if e.kind != "quasigroup" && e.side != some side then continue
    let h := mkConst e.name.toName
    let p ← if isTarget then mkAppM ``characterizes_sideQuasigroup #[h]
      else if e.kind == "quasigroup" then
        mkAppM ``quasigroup_side #[h, mkConst (if side == "left" then ``Side.left else ``Side.right)]
      else if e.kind == "sideQuasigroup" then pure h
      else if e.kind == "term" then mkAppM ``termRecovery_sideQuasigroup #[h]
      else if e.kind == "uniformTerm" then do
        let ci ← getConstInfo e.name.toName
        let ht ← if ci.type.isAppOf ``UniformTermWitness then mkAppM ``uniformTermWitness_recovery #[h]
          else mkAppM ``uniform_implies_term #[h]
        mkAppM ``termRecovery_sideQuasigroup #[ht]
      else continue
    return some (← if e.scope == "all" && scope == "fin" then
      mkAppM ``sideQuasigroup_finite #[p] else pure p)
  return none

private def recoveryOfSide (scope : String) (h : Expr) : MetaM Expr := do
  if scope == "all" then
    mkAppM ``uniform_implies_term #[← mkAppM ``sideQuasigroup_uniform_all #[h]]
  else mkAppM ``sideQuasigroup_term_fin #[h]

private def registerConsequence (source target : Nat) (scope side kind : String)
    (proof : Expr) : MetaM Unit := do
  let env ← getEnv
  if (consequences.getState env).any (fun e => e.source == source && e.target == target &&
      e.scope == scope && e.side == side && e.kind == kind) then return
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "Unresolved metavariable in parastrophe consequence"
  let type ← inferType proof
  -- Module-qualified names prevent collisions when independent imports generate
  -- the same consequence before their environments are combined.
  let name := env.mainModule ++ `parastropheConsequences ++
    Name.mkSimple s!"E{source}_E{target}_{scope}_{side}_{kind}"
  let refs := proof.foldConsts #[] fun n refs =>
    let localSource := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString.startsWith "equational_theories."
      | none => true
    if localSource && ((env.find? n).any (fun ci => ci matches .thmInfo ..)) && !refs.contains n.toString
      then refs.push n.toString else refs
  -- addDecl submits the generated proof term to the kernel. JSON metadata alone
  -- is never sufficient evidence for an arrow.
  addDecl (.thmDecl { name, levelParams := [], type, value := proof })
  modifyEnv (consequences.addEntry · {name := name.toString, source, target, scope, side, kind, refs})

/-- Only type conversions and finite restriction: no graph transitive closure.
Called by each attribute, and once after combining the catalogue's imports. -/
def registerConsequences : MetaM Unit := do
  let entries := results.getState (← getEnv)
  for e in entries do
    unless e.positive && e.status == "PROVED" && e.kind == "singleEquation" do continue
    let some target := e.targetEquation | continue
    let some side := e.side | continue
    for scope in (if e.scope == "all" then #["all", "fin"] else #["fin"]) do
      let h ← if e.scope == "all" && scope == "fin" then
        mkAppM ``characterizes_finite #[mkConst e.name.toName] else pure (mkConst e.name.toName)
      -- The reverse FO arrow does not need source-side bijectivity.
      let back ← mkAppM (if scope == "all" then ``characterizes_structural_backward_all
        else ``characterizes_structural_backward_fin) #[h]
      registerConsequence target e.equation scope side "structural" back
      let some hs ← sideProof? entries e.equation scope side | continue
      let hf ← mkAppM ``characterizes_sameFineSpectrum #[h, hs]
      registerConsequence e.equation target scope side "fineSpectrum" hf
      let inverse ← mkAppM ``characterizes_symm #[h, hs]
      let ht ← mkAppM ``characterizes_sideQuasigroup #[h]
      for (source, dest, hc, hp) in #[(e.equation, target, h, hs), (target, e.equation, inverse, ht)] do
        let term ← recoveryOfSide scope hp
        let ts ← mkAppM (if scope == "all" then ``characterizes_termStructural_all
          else ``characterizes_termStructural_fin) #[hc, term]
        registerConsequence source dest scope side "termStructural" ts
        let fo ← mkAppM (if scope == "all" then ``structural_of_termStructural
          else ``Law.MagmaLaw.structuralFin_of_termStructuralFin) #[ts]
        registerConsequence source dest scope side "structural" fo

private def register (name : Name) (claim : Bool) : IO Unit :=
  registerBuiltinAttribute {
    name
    descr := "Record a precisely typed quasigroup/parastrophe result for the website"
    applicationTime := .afterCompilation
    add := fun decl stx attrKind => do
      unless attrKind == .global do throwError "Parastrophe attributes must be global"
      let ctx ← read
      let line := (stx.getPos?.map fun pos => (ctx.fileMap.toPosition pos).line).getD 1
      let entry ← MetaM.run' (parse decl ctx.fileName line claim)
      modifyEnv (results.addEntry · entry)
      unless claim do MetaM.run' registerConsequences
    erase := fun _ => throwError "Removing parastrophe evidence is not supported"
  }

initialize register `parastrophe_result false
initialize register `parastrophe_claim true

/-- Reconcile evidence registered in separately compiled imported modules. -/
elab "register_parastrophe_consequences" : command =>
  Lean.Elab.Command.liftTermElabM do registerConsequences

end Parastrophes
