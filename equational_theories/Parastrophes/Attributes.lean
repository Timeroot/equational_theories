import equational_theories.Parastrophes.Basic
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
    | ``SingleEquation => pure ("singleEquation", 3)
    | ``Characterizes => pure ("singleEquation", 4)
    | ``TermRecovery => pure ("term", 3)
    | ``UniformTermRecovery => pure ("uniformTerm", 3)
    | ``UniformTermWitness => pure ("uniformTerm", 4)
    | _ => throwError "Expected QuasigroupLaw, SingleEquation, Characterizes, TermRecovery, UniformTermRecovery, or UniformTermWitness (or a negation of a question)"
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
    erase := fun _ => throwError "Removing parastrophe evidence is not supported"
  }

initialize register `parastrophe_result false
initialize register `parastrophe_claim true

end Parastrophes
