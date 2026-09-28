import equational_theories.Spectrum.Equation167

/-! E501 squares each left translation into a semisymmetric operation.
On ordered pairs its rotation is a coordinate swap times a square.
The rotation has order dividing three, so the coordinate swap is even. -/

namespace Spectrum.E501
variable {G : Type*} [Magma G] (h : Equation501 G)

abbrev double (x y : G) : G := x ◇ (x ◇ y)

include h in
theorem semisymmetric (x y : G) : double y (double x y) = x := (h x y).symm

include h in
theorem semisymmetric_dual (x y : G) : double (double x y) x = y := by
  have hh := semisymmetric h y (double x y)
  rwa [semisymmetric h x y] at hh

include h in
theorem row_surjective (x : G) : Function.Surjective (fun y => x ◇ y) := by
  intro y
  exact ⟨x ◇ (y ◇ (y ◇ x)), (h y x).symm⟩

variable [Fintype G]

noncomputable def row (x : G) : Equiv.Perm G :=
  Equiv.ofBijective (fun y => x ◇ y)
    ⟨(Finite.injective_iff_surjective).2 (row_surjective h x), row_surjective h x⟩

def rotation : Equiv.Perm (G × G) where
  toFun p := (double p.1 p.2, p.1)
  invFun p := (p.2, double p.1 p.2)
  left_inv p := Prod.ext rfl (semisymmetric_dual h p.1 p.2)
  right_inv p := Prod.ext (semisymmetric h p.1 p.2) rfl

omit [Fintype G] in
theorem rotation_cube : rotation h * rotation h * rotation h = 1 := by
  ext p
  · change double (double (double p.1 p.2) p.1) (double p.1 p.2) = p.1
    rw [semisymmetric_dual h]
  · exact semisymmetric_dual h p.1 p.2

theorem rotation_factor : rotation h = Equiv.prodComm G G *
    (Equiv.prodCongrRight (row h) * Equiv.prodCongrRight (row h)) := by
  ext p <;> rfl

include h in
theorem swap_even [DecidableEq G] : Equiv.Perm.sign (Equiv.prodComm G G) = 1 := by
  have hs := congrArg Equiv.Perm.sign (rotation_cube h)
  simp only [Equiv.Perm.sign_mul, map_one, Int.units_mul_self, one_mul] at hs
  rw [rotation_factor h, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Int.units_mul_self, mul_one] at hs
  exact hs

include h in
theorem residue [LinearOrder G] : Fintype.card G % 4 = 0 ∨ Fintype.card G % 4 = 1 := by
  have hs := swap_even h
  rw [Bookend.swap_sign] at hs
  have he := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hs
  exact Bookend.residue_of_even (Bookend.card_pairs G) he

/-- info: 'Spectrum.E501.residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms residue
end Spectrum.E501
