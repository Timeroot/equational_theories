import equational_theories.Spectrum.Equation667AffinePrime

/-! An affine E667 algebra whose order is divisible by three has order divisible
by nine. This excludes affine models at all 17 currently unresolved orders. -/
namespace Spectrum.E667.AffineStructure
variable {A : Type*} [AddCommGroup A]

/-- The entire family of orders with exactly one factor of three is excluded
for affine E667 operations over arbitrary finite abelian groups. -/
theorem three_dvd_implies_nine_dvd [Finite A] (f g : AddMonoid.End A) (c : A)
    (h : @Equation667 A ⟨op f g c⟩) (hd : 3 ∣ Nat.card A) : 9 ∣ Nat.card A := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact affine_prime_square_dvd f g c h hd no_root_three

/-- In particular, none of the orders 3 or 6 modulo nine can be affine. -/
theorem not_affine_of_mod_nine [Finite A] (f g : AddMonoid.End A) (c : A)
    (hn : Nat.card A % 9 = 3 ∨ Nat.card A % 9 = 6) :
    ¬ @Equation667 A ⟨op f g c⟩ := by
  intro h
  have h3 : 3 ∣ Nat.card A := Nat.dvd_of_mod_eq_zero (by omega)
  have h9 := Nat.mod_eq_zero_of_dvd (three_dvd_implies_nine_dvd f g c h h3)
  omega

spectrum_assert not_affine_of_mod_nine complete
spectrum_assert three_dvd_implies_nine_dvd complete
end Spectrum.E667.AffineStructure
