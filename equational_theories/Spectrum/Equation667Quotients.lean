import equational_theories.Spectrum.Equation667ConstantDiagonal
import Mathlib.Data.Fintype.Sigma

/-! Abstract facts used to audit proposed small quotients of E667 models.
These results do not rely on the enumeration of small quotient operations. -/

namespace Spectrum.E667.Quotients

variable {A B : Type*} [Magma A] [Magma B] [Finite A] [Finite B]
variable (hA : Equation667 A) (hB : Equation667 B)
variable (π : A → B) (hom : ∀ x y, π (x ◇ y) = π x ◇ π y)
variable (surj : Function.Surjective π)

include hA hB hom surj

/-- Every two fibers of a surjective homomorphism of finite E667 magmas
have the same cardinality. No division operations need be preserved. -/
theorem fiber_card_eq (b c : B) : Nat.card {x : A // π x = b} =
    Nat.card {x : A // π x = c} := by
  have le (b c : B) : Nat.card {x : A // π x = b} ≤ Nat.card {x : A // π x = c} := by
    have hrs : Function.Surjective (fun u : B => u ◇ b) :=
      Finite.injective_iff_surjective.mp (E667883.right_injective667 hB b)
    obtain ⟨u, hu⟩ := hrs c
    dsimp only at hu
    obtain ⟨a, ha⟩ := surj u
    let f : {x : A // π x = b} → {x : A // π x = c} := fun x =>
      ⟨a ◇ x.val, by rw [hom, ha, x.property, hu]⟩
    apply Nat.card_le_card_of_injective f
    intro x y he
    exact Subtype.ext (E667883.left_injective667 hA a (congrArg Subtype.val he))
  exact Nat.le_antisymm (le b c) (le c b)

/-- The quotient order divides the original order, with the common fiber
size as the quotient. -/
theorem card_eq_mul_fiber (b : B) :
    Nat.card A = Nat.card B * Nat.card {x : A // π x = b} := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ c : B, {x : A // π x = c}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = ∑ c : B, Nat.card {x : A // π x = c} := Nat.card_sigma
    _ = ∑ _ : B, Nat.card {x : A // π x = b} := by
      apply Finset.sum_congr rfl
      intro c _
      exact fiber_card_eq hA hB π hom surj c b
    _ = Nat.card B * Nat.card {x : A // π x = b} := by simp [Nat.card_eq_fintype_card]

omit hB surj [Finite B] in
/-- The fiber above an idempotent is a submagma and inherits E667. -/
theorem idempotent_fiber_model (b : B) (hb : b ◇ b = b) :
    Law667.HasModel (Nat.card {x : A // π x = b}) := by
  classical
  let F := {x : A // π x = b}
  letI : Fintype F := Fintype.ofFinite F
  let M : Magma F := ⟨fun x y =>
    ⟨x.val ◇ y.val, by rw [hom, x.property, y.property, hb]⟩⟩
  have hm : @Equation667 F M := by
    intro x y
    exact Subtype.ext (hA x.val y.val)
  exact Law.MagmaLaw.hasModel_of_card M ((@Law667.models_iff _ M).mpr hm)
    (Nat.card_eq_fintype_card.symm)

/-- An idempotent in a quotient forces a model of the complementary factor
of the original cardinality. -/
theorem model_of_idempotent_quotient (b : B) (hb : b ◇ b = b)
    {m k : ℕ} (hm : 0 < m) (ha : Nat.card A = m * k) (hq : Nat.card B = m) :
    Law667.HasModel k := by
  have hc := card_eq_mul_fiber hA hB π hom surj b
  rw [ha, hq] at hc
  have hf : Nat.card {x : A // π x = b} = k := by nlinarith
  rw [← hf]
  exact idempotent_fiber_model hA π hom b hb

spectrum_assert fiber_card_eq complete
spectrum_assert card_eq_mul_fiber complete
spectrum_assert idempotent_fiber_model complete
spectrum_assert model_of_idempotent_quotient complete

end Spectrum.E667.Quotients
