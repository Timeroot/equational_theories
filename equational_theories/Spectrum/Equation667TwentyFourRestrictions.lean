import equational_theories.Spectrum.Equation667FiberEight
import equational_theories.Spectrum.Equation667CommutativePowers

/-! New restrictions at order twenty-four. This does not exclude arbitrary
models at that order: orders twelve and twenty-four remain open. -/
namespace Spectrum.E667

theorem no_eight_quotient_twentyFour {A B : Type*} [Magma A] [Magma B]
    [Finite A] [Finite B] (hA : Equation667 A) (hB : Equation667 B)
    (hc : Nat.card A = 24) (hb : Nat.card B = 8)
    (π : A → B) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = π x ◇ π y) : False := by
  classical
  by_cases hi : ∃ b : B, b ◇ b = b
  · obtain ⟨b,hb'⟩ := hi
    exact not_three_667
      (Quotients.model_of_idempotent_quotient hA hB π hom surj b hb'
        (m := 8) (k := 3) (by decide) (by omega) hb)
  · push Not at hi
    let E : B ≃ Fin 8 := Finite.equivFinOfCardEq hb
    let M : Magma (Fin 8) := (inferInstance : Magma B).relabel E
    letI : Magma (Fin 8) := M
    let e := (inferInstance : Magma B).relabelEquiv E
    have he : Equation667 (Fin 8) := (@Law667.models_iff (Fin 8) M).mp
      ((Law.satisfies_equiv e).mp ((@Law667.models_iff B _).mpr hB))
    have hf (x : Fin 8) : x ◇ x ≠ x := by
      intro hh
      have ht := congrArg e.symm hh
      exact hi (e.symm x) ((e.symm.map_op x x).symm.trans ht)
    obtain ⟨q,hq⟩ := EightClassification.exists_iso he hf
    let P : A → Fin 8 := fun x => q (E (π x))
    apply FiberEight.no_quotient_canonical hA hc P
      (q.surjective.comp (E.surjective.comp surj))
    intro x y
    change q (E (π (x ◇ y))) = _
    rw [hom]
    change q (e (π x ◇ π y)) = _
    exact (congrArg q (e.map_op (π x) (π y))).trans (hq _ _)

/-- At order twenty-four, the only possible proper nontrivial quotient
orders are two and twelve. In either case an order-twelve model must exist. -/
theorem quotient_card_twentyFour {A B : Type*} [Magma A] [Magma B]
    [Finite A] [Finite B] (hA : Equation667 A) (hB : Equation667 B)
    (hc : Nat.card A = 24) (π : A → B) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = π x ◇ π y) :
    Nat.card B = 1 ∨ Nat.card B = 2 ∨ Nat.card B = 12 ∨ Nat.card B = 24 := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨a⟩ : Nonempty A := Finite.card_pos_iff.mp (by omega)
  have factor := Quotients.card_eq_mul_fiber hA hB π hom surj (π a)
  have hd : Nat.card B ∣ 24 :=
    ⟨Nat.card {x : A // π x = π a}, by simpa only [hc] using factor⟩
  have cases : Nat.card B = 1 ∨ Nat.card B = 2 ∨ Nat.card B = 3 ∨
      Nat.card B = 4 ∨ Nat.card B = 6 ∨ Nat.card B = 8 ∨
      Nat.card B = 12 ∨ Nat.card B = 24 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : (24 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by decide +kernel] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have modelB : Law667.HasModel (Nat.card B) :=
    Law.MagmaLaw.hasModel_of_card (inferInstance : Magma B)
      ((@Law667.models_iff B _).mpr hB) Nat.card_eq_fintype_card.symm
  rcases cases with h1 | h2 | h3 | h4 | h6 | h8 | h12 | h24
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact False.elim (not_three_667 (h3 ▸ modelB))
  · obtain ⟨b,hb⟩ := SmallQuotients.exists_idempotent_of_card hB (Or.inr h4)
    exact False.elim (E667883.not_order_667_6
      (Quotients.model_of_idempotent_quotient hA hB π hom surj b hb
        (m := 4) (k := 6) (by decide) (by omega) h4))
  · exact False.elim (E667883.not_order_667_6 (h6 ▸ modelB))
  · exact False.elim (no_eight_quotient_twentyFour hA hB hc h8 π surj hom)
  · exact Or.inr (Or.inr (Or.inl h12))
  · exact Or.inr (Or.inr (Or.inr h24))

/-- A nonsimple order-twenty-four model would already resolve order twelve
positively, through either a quotient or an idempotent fiber. -/
theorem model_twelve_of_proper_quotient_twentyFour {A B : Type*}
    [Magma A] [Magma B] [Finite A] [Finite B]
    (hA : Equation667 A) (hB : Equation667 B) (hc : Nat.card A = 24)
    (π : A → B) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = π x ◇ π y)
    (hb : 1 < Nat.card B) (hlt : Nat.card B < 24) : Law667.HasModel 12 := by
  classical
  rcases quotient_card_twentyFour hA hB hc π surj hom with h1 | h2 | h12 | h24
  · omega
  · obtain ⟨b,he⟩ := SmallQuotients.exists_idempotent_of_card hB (Or.inl h2)
    exact Quotients.model_of_idempotent_quotient hA hB π hom surj b he
      (m := 2) (k := 12) (by decide) (by omega) h2
  · letI : Fintype B := Fintype.ofFinite B
    exact Law.MagmaLaw.hasModel_of_card (inferInstance : Magma B)
      ((@Law667.models_iff B _).mpr hB)
      (by simpa only [Nat.card_eq_fintype_card] using h12)
  · omega

/-- The order-twenty-four instance of the general commutative obstruction. -/
theorem not_commutative_twentyFour {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hcard : Nat.card A = 24) :
    ¬ ∀ x y : A, x ◇ y = y ◇ x :=
  not_commutative_three_mul_power_two h 3 (by norm_num; exact hcard)

spectrum_assert not_commutative_twentyFour complete
spectrum_assert no_eight_quotient_twentyFour complete
spectrum_assert quotient_card_twentyFour complete
spectrum_assert model_twelve_of_proper_quotient_twentyFour complete
end Spectrum.E667
