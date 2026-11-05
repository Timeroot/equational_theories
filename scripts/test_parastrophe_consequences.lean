import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.Basic

/-! Isolated registry: no populated catalogue is imported. Test missing premises,
declaration order, side/scope separation, claims, and generated proof types. -/
open Parastrophes Law FreeMagma Lean Elab Command

private theorem division14 {G : Type} (M : Magma G) (h : @Equation14 G M) :
    IsDivision .left M (opposite M) ∧ IsDivision .right M (opposite M) := by
  have cyclic (x y : G) : M.op (M.op x y) x = y := by
    have hh := h y (M.op x y)
    rw [← h x y] at hh
    exact hh.symm
  exact ⟨⟨fun x y => (h y x).symm, cyclic⟩,
    ⟨fun x y => cyclic y x, fun x y => (h x y).symm⟩⟩

@[parastrophe_result] theorem imageFirst : Characterizes .all Law14 .left Law29 := by
  intro G D _
  constructor
  · intro h
    have hm : @satisfies _ G (opposite D) Law14 :=
      (@Law14.models_iff G (opposite D)).mpr ((@Law29.models_iff G D).mp h)
    exact ⟨opposite D, hm, (division14 (opposite D) ((@Law14.models_iff G (opposite D)).mp hm)).1⟩
  · rintro ⟨M, hm, hd⟩
    have h14 := (@Law14.models_iff _ _).mp hm
    have he := division_unique hd (division14 M h14).1
    subst D
    exact (@Law29.models_iff G (opposite M)).mpr h14

private def checkIncomplete : Lean.Elab.Term.TermElabM Unit := do
  let facts := consequences.getState (← getEnv)
  unless facts.size == 2 && facts.all (fun c =>
      c.source == 29 && c.target == 14 && c.kind == "structural") do
    throwError "Exact image without source bijectivity must give only the reverse FO arrows"

run_elab checkIncomplete

/-- Deliberately registered only as a claim, despite having an actual proof. -/
@[parastrophe_claim] theorem claimedLeft : SideQuasigroupLaw .all Law14 .left := by
  intro G M _ h
  exact sideQuasigroup_of_division (division14 M ((@Law14.models_iff _ _).mp h)).1

@[parastrophe_result] theorem wrongSide : SideQuasigroupLaw .all Law14 .right := by
  intro G M _ h
  exact sideQuasigroup_of_division (division14 M ((@Law14.models_iff _ _).mp h)).2

run_elab checkIncomplete

@[parastrophe_result] theorem finiteTermLater : TermRecovery .fin Law14 .left := by
  intro G M _ h
  exact ⟨Lf 1 ⋆ Lf 0, (division14 M ((@Law14.models_iff _ _).mp h)).1⟩

run_elab do
  let facts := consequences.getState (← getEnv)
  unless facts.any (fun c => c.kind == "fineSpectrum" && c.scope == "fin") do
    throwError "Later finite term evidence failed to generate fine-spectrum equivalence"
  for (s,t) in [(14,29),(29,14)] do
    unless facts.any (fun c => c.kind == "termStructural" && c.scope == "fin" &&
        c.source == s && c.target == t) do
      throwError "Missing finite term-structural arrow"
  if facts.any (fun c => c.scope == "all" && c.kind != "structural") then
    throwError "Finite term, right-side proof, or conjecture leaked into all-carrier evidence"

@[parastrophe_result] theorem uniformTermLast :
    UniformTermWitness .all Law14 .left (Lf 1 ⋆ Lf 0) := by
  intro G M _ h
  exact (division14 M ((@Law14.models_iff _ _).mp h)).1

run_elab do
  let facts := consequences.getState (← getEnv)
  unless facts.any (fun c => c.kind == "fineSpectrum" && c.scope == "all") do
    throwError "Uniform term did not upgrade the arbitrary-carrier facts"
  for c in facts do
    for ax in ← Lean.collectAxioms c.name.toName do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unapproved axiom in generated theorem: {ax}"
    -- Check the *actual types*, not merely the emitted JSON fields.
    if c.kind == "termStructural" && c.scope == "all" && c.source == 14 && c.target == 29 then
      do
        let expected ← Lean.Meta.mkAppM ``Law.MagmaLaw.TermStructuralFrom #[mkConst ``Law29, mkConst ``Law14]
        unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType (mkConst c.name.toName)) expected do
          throwError "Generated arrow has the wrong orientation/type"
  registerConsequences
  unless (consequences.getState (← getEnv)).size == facts.size do
    throwError "Repeated registration duplicated consequences"
