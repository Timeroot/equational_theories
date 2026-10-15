import equational_theories.Definability.ComposedDiagonalSwaps

/-! E327 says that multiplying an entry again on the right does not change
its column. A sequence of three reversible output swaps turns each row into
an idempotent map, giving an E323 companion on the same carrier. -/
open Law Law.MagmaLaw DiagonalOutputSwap
set_option maxHeartbeats 500000
namespace AbsorptionRows

noncomputable abbrev companion {G : Type} (M : Magma G) : Magma G :=
  (forward 3 1 false).magma ((forward 0 3 false).magma ((forward 2 0 false).magma M))

open scoped Classical in
/-- The source law simplifies three output swaps to this short decision tree. -/
theorem companion_apply {G : Type} (M : Magma G) (h : @Equation327 G M) (x y : G) :
    (companion M).op x y = if x = y then M.op x x else
      if M.op x y = M.op x x then y else if M.op x y = x then M.op x x else M.op x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  let q := M.op x x
  let r := M.op y y
  let t := M.op x y
  have h1 : M.op x t = q := (h x x y).symm
  have h2 : M.op x q = q := (h x x x).symm
  have h3 : M.op x r = t := (h x y y).symm
  clear h
  have ty : t = y → t = q := by intro he; change M.op x y = q; rwa [he] at h1
  have tr : t = r → t = q := by intro he; grind
  have qr : q = r → t = q := by intro he; grind
  have qy : q = y → t = q := by
    intro he
    exact (congrArg (M.op x) he.symm).trans h2
  have hn : (companion M).op x y = Equiv.swap r y (Equiv.swap x r (Equiv.swap q x t)) := by
    simp [forward_apply, value, hxy, q, r, t]
  rw [hn, if_neg hxy]
  change Equiv.swap r y (Equiv.swap x r (Equiv.swap q x t)) =
    if t = q then y else if t = x then q else t
  by_cases htq : t = q
  · simp [htq]
  by_cases htx : t = x
  · have hqx : q ≠ x := by grind
    have hqr : q ≠ r := by intro he; exact htq (qr he)
    have hqy : q ≠ y := by intro he; exact htq (qy he)
    simp [htx,hqx,Ne.symm hqx,hqr,hqy,Equiv.swap_apply_def]
  · have htr : t ≠ r := by intro he; exact htq (tr he)
    have hty : t ≠ y := by intro he; exact htq (ty he)
    simp [htq,htx,htr,hty,Equiv.swap_apply_def]

/-- Every value in a row of the companion is fixed by that row. -/
theorem target323 {G : Type} (M : Magma G) (h : @Equation327 G M) :
    @Equation323 G (companion M) := by
  classical
  have fixed_square (x : G) : (companion M).op x (M.op x x) = M.op x x := by
    rw [companion_apply M h]
    have hh := (h x x x).symm
    split_ifs <;> grind
  intro x y
  have ht := (h x x y).symm
  rw [companion_apply M h x y]
  split_ifs with hxy htq htx
  · subst y
    exact (fixed_square x).symm
  · simp only [companion_apply M h, if_neg hxy, if_pos htq]
  · exact (fixed_square x).symm
  · rw [companion_apply M h, if_neg (Ne.symm htx), if_pos ht]
theorem Equation323_structuralFrom_Equation327_absorptionRows :
    Law323.StructuralFrom Law327 :=
  structuralFrom_threeDiagonalSwaps 2 0 0 3 3 1 false fun {G} M hM =>
    (@Law323.models_iff G (companion M)).mpr
      (target323 M ((@Law327.models_iff G M).mp hM))

end AbsorptionRows

/-- info: 'AbsorptionRows.Equation323_structuralFrom_Equation327_absorptionRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AbsorptionRows.Equation323_structuralFrom_Equation327_absorptionRows
