import equational_theories.Spectrum.Equation467Translations
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! A proper submagma of a finite quasigroup has at most half its elements.
For the remaining order-16 E467 search cases, the idempotents are a proper
majority. Hence two idempotents must have nonidempotent product. This gives
three distinguished elements for sound symmetry breaking. -/
namespace Spectrum.E467

variable {G : Type*} [Finite G] (p : G → G → G)
  (h : ∀ x y, x = p y (p x (p x (p y y))))

include h

/-- A proper subset with more than half the elements cannot be closed. -/
theorem large_subset_not_closed (s : Finset G) (x : G) (hx : x ∉ s)
    (hs : Nat.card G < 2*s.card) : ∃ a ∈ s, ∃ b ∈ s, p a b ∉ s := by
  classical
  letI := Fintype.ofFinite G
  by_contra hn
  push Not at hn
  have hout (b : G) (hb : b ∈ s) : p x b ∉ s := by
    intro hp
    let f : s → s := fun a => ⟨p a b, hn a a.property b hb⟩
    have hf : Function.Injective f := by
      intro a c he
      exact Subtype.ext (right_injective p h b (congrArg Subtype.val he))
    obtain ⟨a,ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨p x b,hp⟩
    have he : p a.val b = p x b := congrArg Subtype.val ha
    exact hx ((right_injective p h b he) ▸ a.property)
  have hi : s.image (p x) ⊆ sᶜ := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_compl.mpr (hout b hb)
  have hc := Finset.card_le_card hi
  rw [Finset.card_image_of_injective s (left_injective p h x), Finset.card_compl] at hc
  rw [Nat.card_eq_fintype_card] at hs
  omega

end Spectrum.E467
