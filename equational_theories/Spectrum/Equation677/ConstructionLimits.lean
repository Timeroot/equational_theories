import equational_theories.Spectrum.QuarticSeeds
import Mathlib.Tactic.LinearCombination

/-! The existing idempotent and commuting-scalar affine constructions cannot
refute the finite E677 → E255 question. E255 is already true in every
idempotent magma, and an explicit polynomial identity handles all scalar-
affine E677 magmas over arbitrary commutative rings. No finiteness is used. -/

namespace Spectrum.E677.ConstructionLimits

/-- E255 is a one-variable identity, hence automatic under idempotence. -/
theorem equation255_of_idempotent {G : Type*} [Magma G]
    (h : ∀ x : G, x ◇ x = x) : Equation255 G := by
  intro x
  rw [h x, h x, h x]

/-- Every companion operation used for the fourth-power seeds satisfies E255,
regardless of the companion polynomial, since it is idempotent. -/
theorem quartic_equation255 {R : Type*} [CommRing R] (c0 c1 c2 c3 : R) :
    @Equation255 (R × R × R × R) ⟨QuarticSeeds.op c0 c1 c2 c3⟩ :=
  @equation255_of_idempotent (R × R × R × R) ⟨QuarticSeeds.op c0 c1 c2 c3⟩
    (QuarticSeeds.idempotent c0 c1 c2 c3)

@[implicit_reducible] def affine {R : Type*} [CommRing R] (a b c : R) : Magma R :=
  ⟨fun x y => a*x+b*y+c⟩

/-- The E255 linear coefficient lies in the ideal of the E677 coefficients. -/
theorem coefficient_identity {R : Type*} [CommRing R] (a b : R) :
    (a+b-1)*(a^2+a+1) =
      (-a^3*b-a^2-a*b^2-b+1)*(a*b^3+a*b-1) +
      (a*(a*b^2+a+b-1))*(a^2*b^2+a+b^3) := by ring

/-- The corresponding ideal identity for the constant coefficient. -/
theorem constant_identity {R : Type*} [CommRing R] (a b : R) :
    a^2+a+1 =
      (-a^2*b-a*b-a-2)*(a*b^3+a*b-1) +
      (a*b^2+a+b^2+b)*(a^2*b^2+a+b^3) +
      (-b^3+b-1)*(a*b^2+b^2+b+1) := by ring

/-- No scalar-affine operation over a commutative ring can refute E677 → E255.
This includes nonidempotent operations, constant terms, zero divisors, and
infinite rings. The proof uses neither cancellation nor a field hypothesis. -/
theorem affine_equation255 {R : Type*} [CommRing R] (a b c : R)
    (h : @Equation677 R (affine a b c)) : @Equation255 R (affine a b c) := by
  have h00 := h 0 0
  have h10 := h 1 0
  have h01 := h 0 1
  change 0 = a*0+b*(a*0+b*(a*(a*0+b*0+c)+b*0+c)+c)+c at h00
  change 1 = a*0+b*(a*1+b*(a*(a*0+b*1+c)+b*0+c)+c)+c at h10
  change 0 = a*1+b*(a*0+b*(a*(a*1+b*0+c)+b*1+c)+c)+c at h01
  have hP : a*b^3+a*b-1 = 0 := by linear_combination h00-h10
  have hQ : a^2*b^2+a+b^3 = 0 := by linear_combination h00-h01
  have hC : c*(a*b^2+b^2+b+1) = 0 := by linear_combination -h00
  have hT : (a+b-1)*(a^2+a+1) = 0 := by
    rw [coefficient_identity, hP, hQ]
    ring
  have hU : c*(a^2+a+1) = 0 := by
    rw [constant_identity, mul_add, mul_add, hP, hQ]
    rw [show c*((-b^3+b-1)*(a*b^2+b^2+b+1)) =
      (-b^3+b-1)*(c*(a*b^2+b^2+b+1)) by ring, hC]
    ring
  intro x
  change x = a*(a*(a*x+b*x+c)+b*x+c)+b*x+c
  linear_combination -x*hT-hU

spectrum_assert equation255_of_idempotent complete
spectrum_assert quartic_equation255 complete
spectrum_assert affine_equation255 complete

/-- info: 'Spectrum.E677.ConstructionLimits.equation255_of_idempotent' does not depend on any axioms -/
#guard_msgs in
#print axioms equation255_of_idempotent
/-- info: 'Spectrum.E677.ConstructionLimits.quartic_equation255' depends on axioms: [propext] -/
#guard_msgs in
#print axioms quartic_equation255
/-- info: 'Spectrum.E677.ConstructionLimits.affine_equation255' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms affine_equation255

end Spectrum.E677.ConstructionLimits
