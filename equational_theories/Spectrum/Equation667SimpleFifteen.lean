import equational_theories.Spectrum.Equation667SimpleTwelve
import equational_theories.Spectrum.Equation667FiveClassification.Certificate

/-! Every order-fifteen E667 model is simple. A five-element quotient either
has a forbidden three-element idempotent fiber, or is the now fully classified
idempotent-free quotient, whose three-element-fiber extensions are impossible. -/
namespace Spectrum.E667

private theorem no_five_quotient {A B : Type*} [Magma A] [Magma B]
    [Finite A] [Finite B] (hA : Equation667 A) (hB : Equation667 B)
    (hc : Nat.card A = 15) (hb : Nat.card B = 5)
    (π : A → B) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = π x ◇ π y) : False := by
  classical
  by_cases hi : ∃ b : B, b ◇ b = b
  · obtain ⟨b,hb'⟩ := hi
    exact not_three_667
      (Quotients.model_of_idempotent_quotient hA hB π hom surj b hb'
        (m := 5) (k := 3) (by decide) (by omega) hb)
  · push Not at hi
    let E : B ≃ Fin 5 := Finite.equivFinOfCardEq hb
    let M : Magma (Fin 5) := (inferInstance : Magma B).relabel E
    letI : Magma (Fin 5) := M
    let e := (inferInstance : Magma B).relabelEquiv E
    have he : Equation667 (Fin 5) := (@Law667.models_iff (Fin 5) M).mp
      ((Law.satisfies_equiv e).mp ((@Law667.models_iff B _).mpr hB))
    have hf (x : Fin 5) : x ◇ x ≠ x := by
      intro hh
      have ht := congrArg e.symm hh
      exact hi (e.symm x) ((e.symm.map_op x x).symm.trans ht)
    obtain ⟨q,hq⟩ := FiveClassification.exists_iso he hf
    let P : A → Fin 5 := fun x => q (E (π x))
    apply FiberThree.no_quotient_five hA hc P
      (q.surjective.comp (E.surjective.comp surj))
    intro x y
    change q (E (π (x ◇ y))) = _
    rw [hom]
    change q (e (π x ◇ π y)) = _
    exact (congrArg q (e.map_op (π x) (π y))).trans (hq _ _)

/-- A fifteen-element E667 magma has no proper nontrivial quotient. -/
theorem quotient_card_fifteen {A B : Type*} [Magma A] [Magma B]
    [Finite A] [Finite B] (hA : Equation667 A) (hB : Equation667 B)
    (hc : Nat.card A = 15) (π : A → B) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = π x ◇ π y) :
    Nat.card B = 1 ∨ Nat.card B = 15 := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨a⟩ : Nonempty A := Finite.card_pos_iff.mp (by omega)
  have factor := Quotients.card_eq_mul_fiber hA hB π hom surj (π a)
  have hd : Nat.card B ∣ 15 :=
    ⟨Nat.card {x : A // π x = π a}, by simpa only [hc] using factor⟩
  have cases : Nat.card B = 1 ∨ Nat.card B = 3 ∨ Nat.card B = 5 ∨ Nat.card B = 15 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : (15 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide +kernel] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases cases with h1 | h3 | h5 | h15
  · exact Or.inl h1
  · apply False.elim
    apply not_three_667
    exact Law.MagmaLaw.hasModel_of_card (inferInstance : Magma B)
      ((@Law667.models_iff B _).mpr hB) (by simpa only [Nat.card_eq_fintype_card] using h3)
  · exact False.elim (no_five_quotient hA hB hc h5 π surj hom)
  · exact Or.inr h15

spectrum_assert quotient_card_fifteen complete
end Spectrum.E667
