import Mathlib.Algebra.Group.Hom.Basic

/-! Affine operations over arbitrary groups: E1483 forces E168, including
nonabelian groups, noncommuting endomorphisms, and a constant offset.
See docs/1483_general_constructions.md for the structural interpretation. -/

namespace Spectrum.E1483.GroupAffine
variable {G : Type*} [Group G] (A B : G →* G) (c : G)
def operation (x y : G) : G := A x * B y * c

variable (h : ∀ x y z, operation A B c (operation A B c y x)
    (operation A B c x (operation A B c y z)) = x)

include h in
/-- An affine E1483 operation over any group satisfies the central law E168. -/
theorem central : ∀ x y z, operation A B c (operation A B c y x)
    (operation A B c x z) = x := by
  have expand (x y z : G) :
      A (A y) * A (B x) * A c * B (A x) * B (B (A y)) * B (B (B z)) *
        B (B c) * B c * c = x := by
    have hh := h x y z
    simpa only [operation, map_mul, mul_assoc] using hh
  have hc : A c * B (B c) * B c * c = 1 := by
    simpa only [map_one, one_mul, mul_one] using expand 1 1 1
  have b3 (z : G) : B (B (B z)) = 1 := by
    have hz := expand 1 1 z
    simp only [map_one, one_mul, mul_one] at hz
    have he : A c * B (B (B z)) * (B (B c) * B c * c) =
        A c * 1 * (B (B c) * B c * c) := by
      simpa only [mul_assoc, mul_one] using hz.trans hc.symm
    exact mul_left_cancel (mul_right_cancel he)
  have reduced (x y : G) :
      A (A y) * A (B x) * A c * B (A x) * B (B (A y)) = x * A c := by
    have hh := expand x y 1
    simp only [map_one, mul_one] at hh
    have hc' : B (B c) * B c * c = (A c)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      simpa only [mul_assoc] using hc
    have hh' : (A (A y) * A (B x) * A c * B (A x) * B (B (A y))) *
        (A c)⁻¹ = x := by
      simpa only [← hc', mul_assoc] using hh
    exact (mul_inv_eq_iff_eq_mul).1 hh'
  have decomp (x : G) : A (B x) * A c * B (A x) = x * A c := by
    simpa only [map_one, one_mul, mul_one] using reduced x 1
  have a2 (y : G) : A (A y) * A c * B (B (A y)) = A c := by
    simpa only [map_one, one_mul, mul_one] using reduced 1 y
  have ba2 (y : G) : B (A (A y)) = 1 := by
    have hh := congrArg B (a2 y)
    simp only [map_mul, b3, mul_one] at hh
    exact (mul_eq_right).1 hh
  have aba (x : G) : A (B (A x)) = A x := by
    have hh := decomp (A x)
    simpa only [ba2, mul_one, mul_left_inj] using hh
  have commutes (x y : G) : A (A y) * x = x * A (A y) := by
    have hh := reduced x y
    rw [mul_assoc (A (A y)) (A (B x)),
      mul_assoc (A (A y)) (A (B x) * A c)] at hh
    rw [decomp] at hh
    have ha := a2 y
    have hi : A c * B (B (A y)) = (A (A y))⁻¹ * A c := by
      exact (eq_inv_mul_iff_mul_eq).2 (by simpa only [mul_assoc] using ha)
    have hh' : A (A y) * x * (A (A y))⁻¹ = x := by
      apply mul_right_cancel (b := A c)
      simpa only [mul_assoc, hi] using hh
    exact (mul_inv_eq_iff_eq_mul).1 hh'
  have a2b (x : G) : A (A (B x)) = 1 := by
    have hh := congrArg A (decomp x)
    simp only [map_mul, aba] at hh
    rw [mul_assoc, commutes (A x) c] at hh
    have he : A (A (B x)) * (A x * A (A c)) = 1 * (A x * A (A c)) := by
      simpa only [mul_assoc, one_mul] using hh
    exact mul_right_cancel he
  have b2ab (x : G) : B (B (A (B x))) = 1 := by
    have hh := a2 (B x)
    simp only [a2b, one_mul] at hh
    exact (mul_eq_left).1 hh
  have b2 (x : G) : B (B x) = 1 := by
    have hh := congrArg (fun t => B (B t)) (decomp x)
    simp only [map_mul, b2ab, b3, one_mul, mul_one] at hh
    exact ((mul_eq_right).1 hh.symm)
  have a2one (x : G) : A (A x) = 1 := by
    have hh := a2 x
    simpa only [b2, mul_one, mul_eq_right] using hh
  have hc' : A c * B c * c = 1 := by
    simpa only [b2, mul_one] using hc
  intro x y z
  simp only [operation, map_mul, a2one, b2, one_mul, mul_one]
  rw [← mul_assoc (A (B x) * A c) (B (A x)), decomp]
  simp only [mul_assoc, hc', mul_one]

/-- The affine instances of the two laws coincide, without a finiteness hypothesis. -/
theorem lawful_iff_central :
    (∀ x y z, operation A B c (operation A B c y x)
      (operation A B c x (operation A B c y z)) = x) ↔
    (∀ x y z, operation A B c (operation A B c y x)
      (operation A B c x z) = x) :=
  ⟨central A B c, fun hh x y z => hh x y (operation A B c y z)⟩

/-- info: 'Spectrum.E1483.GroupAffine.central' depends on axioms: [propext] -/
#guard_msgs in
#print axioms central
end Spectrum.E1483.GroupAffine
