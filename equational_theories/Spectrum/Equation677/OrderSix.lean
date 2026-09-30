import equational_theories.Spectrum.Equation677.OrderSix.Idempotent
import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status

/-! No six-element E677 magma. The proof supplied in PR #6 is integrated using
Mathlib finite types and minimal periods, with ordinary equational case proofs. -/
namespace Spectrum

/-- The order-six exclusion on any finite carrier, independent of its enumeration. -/
theorem E677.card_ne_six {G : Type*} [Magma G] [Finite G] (h : Equation677 G) :
    Nat.card G ≠ 6 := by
  letI : Fact (Equation677 G) := ⟨h⟩
  exact OrderSix.card_ne_six

theorem not_order_677_6 : ¬ Law677.HasModel 6 := by
  rintro ⟨M, hM⟩
  letI := M
  exact E677.card_ne_six ((@Law677.models_iff _ M).mp hM) (by simp)

spectrum_assert not_order_677_6 complete
/-- info: 'Spectrum.not_order_677_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_order_677_6
end Spectrum
