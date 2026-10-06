import equational_theories.Spectrum.Equation667CommutativeParity

/-! The order-fifteen exclusion is a corollary of the general parity theorem.
This replaces the former 8.6 MB LRAT certificate. No finite enumeration,
certificate decoder, or native computation is needed. -/
namespace Spectrum.E667

/-- Commutative E667 magmas of order fifteen are impossible. -/
theorem not_commutative_fifteen {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hcard : Nat.card A = 15) :
    ¬ ∀ x y : A, x ◇ y = y ◇ x :=
  not_commutative_of_card_mod_four_three h (by rw [hcard])

spectrum_assert not_commutative_fifteen complete
end Spectrum.E667
