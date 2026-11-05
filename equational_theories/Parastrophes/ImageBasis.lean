import equational_theories.Parastrophes.Basic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Exact descriptions of division images by several equations

These are supplementary records, not positive answers to `SingleEquation`.
Each registered theorem states an exact equivalence among all magmas in its
scope, without assuming beforehand that the candidate operation has division.
-/
namespace Parastrophes
open Law Lean Meta

/-- An exact finite list of identities for the actual division image. -/
def CharacterizesBasis (scope : Scope) (L : NatMagmaLaw) (side : Side)
    (targets : List NatMagmaLaw) : Prop :=
  ∀ (G : Type) (D : Magma G), scope.Allows G →
    ((∀ t ∈ targets, @satisfies _ G D t) ↔ InImage L side D)

theorem imageBasis_finite {L side targets}
    (h : CharacterizesBasis .all L side targets) :
    CharacterizesBasis .fin L side targets := fun G D _ => h G D trivial

theorem imageBasis_dual {scope L side targets}
    (h : CharacterizesBasis scope L side targets) :
    CharacterizesBasis scope L.dual side.swap (targets.map MagmaLaw.dual) := by
  intro G D hG
  have hs : (∀ t ∈ targets.map MagmaLaw.dual, @satisfies _ G D t) ↔
      ∀ t ∈ targets, @satisfies _ G (opposite D) t := by
    simp only [List.forall_mem_map]
    exact forall_congr' fun t => forall_congr' fun _ => satisfies_opposite (opposite D) t
  exact hs.trans ((h G (opposite D) hG).trans (inImage_dual L side (opposite D)).symm)

theorem imageBasis_of_equivalent {scope L K side targets}
    (hI : ImpliesIn scope L K) (hJ : ImpliesIn scope K L)
    (h : CharacterizesBasis scope K side targets) :
    CharacterizesBasis scope L side targets := by
  intro G D hG
  refine (h G D hG).trans ?_
  constructor <;> rintro ⟨M, hm, hd⟩
  · exact ⟨M, hJ G M hG hm, hd⟩
  · exact ⟨M, hI G M hG hm, hd⟩

structure ImageBasisEntry where
  name : String
  file : String
  line : Nat
  equation : Nat
  scope : String
  side : String
  targetLaws : List NatMagmaLaw
  status : String := "PROVED"
  description : String := ""
  deriving ToJson

initialize imageBases : SimplePersistentEnvExtension ImageBasisEntry (Array ImageBasisEntry) ←
  registerSimplePersistentEnvExtension {
    name := `Parastrophes.imageBases
    addImportedFn := Array.flatMap id
    addEntryFn := Array.push
  }

private def parseBasis (decl : Name) (file : String) (line : Nat) : MetaM ImageBasisEntry := do
  let .thmInfo info ← getConstInfo decl | throwError "An image basis must be a theorem"
  unless info.type.isAppOfArity ``CharacterizesBasis 4 do
    throwError "Expected an unconditional CharacterizesBasis theorem"
  let args := info.type.getAppArgs
  let some name := args[1]!.constName? | throwError "Use a catalogue source law"
  let str := name.toString
  let some equation := (str.drop 3).toString.toNat? | throwError "Use a catalogue source law"
  unless str.startsWith "Law" && 1 ≤ equation && equation ≤ 4694 do
    throwError "Use a catalogue source law"
  let scopeExpr ← whnf args[0]!
  let scope ← if scopeExpr.isConstOf ``Scope.all then pure "all"
    else if scopeExpr.isConstOf ``Scope.fin then pure "fin"
    else throwError "Expected scope .all or .fin"
  let sideExpr ← whnf args[2]!
  let side ← if sideExpr.isConstOf ``Side.left then pure "left"
    else if sideExpr.isConstOf ``Side.right then pure "right"
    else throwError "Expected side .left or .right"
  let targetLaws ← unsafe evalExpr (List NatMagmaLaw) (← inferType args[3]!) args[3]!
  unless targetLaws.length ≥ 2 do
    throwError "Use parastrophe_result for a single-equation characterization"
  for ax in ← Lean.collectAxioms decl do
    unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
      throwError "Image-basis evidence uses an unapproved axiom: {ax}"
  return {
    name := decl.toString
    file := file
    line := line
    equation := equation
    scope := scope
    side := side
    targetLaws := targetLaws
    description := (← findDocString? (← getEnv) decl).getD ""
  }

initialize registerBuiltinAttribute {
  name := `parastrophe_basis
  descr := "Record a proved exact characterization by several magma identities"
  applicationTime := .afterCompilation
  add := fun decl stx attrKind => do
    unless attrKind == .global do throwError "Image-basis attributes must be global"
    let ctx ← read
    let line := (stx.getPos?.map fun pos => (ctx.fileMap.toPosition pos).line).getD 1
    let entry ← MetaM.run' (parseBasis decl ctx.fileName line)
    modifyEnv (imageBases.addEntry · entry)
  erase := fun _ => throwError "Removing image-basis evidence is not supported"
}

end Parastrophes
