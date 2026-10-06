import equational_theories.Spectrum.Equation667Quotients
import equational_theories.Spectrum.Equation667SmallQuotients
import equational_theories.Spectrum.Equation667883Small.Six667
import equational_theories.Spectrum.Generated.SmallOrder
import Mathlib.NumberTheory.Divisors

/-! Every hypothetical twelve-element E667 magma is simple: a surjective
homomorphism has either a one-element target or a twelve-element target.
This is a structural restriction, not a nonexistence theorem at order twelve.
-/

namespace Spectrum.E667

/-- A twelve-element E667 magma has no proper nontrivial finite quotient. -/
theorem quotient_card_twelve {A B : Type*} [Magma A] [Magma B]
    [Finite A] [Finite B] (hA : Equation667 A) (hB : Equation667 B)
    (hc : Nat.card A = 12) (π : A → B) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = π x ◇ π y) :
    Nat.card B = 1 ∨ Nat.card B = 12 := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨a⟩ : Nonempty A := Finite.card_pos_iff.mp (by omega)
  have factor := Quotients.card_eq_mul_fiber hA hB π hom surj (π a)
  have hd : Nat.card B ∣ 12 :=
    ⟨Nat.card {x : A // π x = π a}, by simpa only [hc] using factor⟩
  have cases : Nat.card B = 1 ∨ Nat.card B = 2 ∨ Nat.card B = 3 ∨
      Nat.card B = 4 ∨ Nat.card B = 6 ∨ Nat.card B = 12 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : (12 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide +kernel] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have modelB : Law667.HasModel (Nat.card B) :=
    Law.MagmaLaw.hasModel_of_card (inferInstance : Magma B)
      ((@Law667.models_iff B _).mpr hB) Nat.card_eq_fintype_card.symm
  rcases cases with h1 | h2 | h3 | h4 | h6 | h12
  · exact Or.inl h1
  · obtain ⟨b, hb⟩ := SmallQuotients.exists_idempotent_of_card hB (Or.inl h2)
    exact False.elim (E667883.not_order_667_6
      (Quotients.model_of_idempotent_quotient hA hB π hom surj b hb
        (m := 2) (k := 6) (by decide) (by omega) h2))
  · exact False.elim (not_three_667 (h3 ▸ modelB))
  · obtain ⟨b, hb⟩ := SmallQuotients.exists_idempotent_of_card hB (Or.inr h4)
    exact False.elim (not_three_667
      (Quotients.model_of_idempotent_quotient hA hB π hom surj b hb
        (m := 4) (k := 3) (by decide) (by omega) h4))
  · exact False.elim (E667883.not_order_667_6 (h6 ▸ modelB))
  · exact Or.inr h12

spectrum_assert quotient_card_twelve complete

end Spectrum.E667
