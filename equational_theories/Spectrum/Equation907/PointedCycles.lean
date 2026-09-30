import equational_theories.Spectrum.Equation907

/-! In a finite E907 model, the cycle of `a` under left multiplication by `a`
is either a fixed point or has length at least five. These are direct equational
proofs; the model-search answers that suggested them are not proof inputs. -/
namespace Spectrum.E907
variable {G : Type*} [Magma G] [Finite G]

/-- The inverse left translation can be written as a magma term. -/
theorem inverse_left_identity (h : Equation907 G) (a x : G) :
    (a ◇ (a ◇ x)) ◇ ((a ◇ x) ◇ a) = x :=
  ((left_division h a (a ◇ x) x).mp rfl).symm

/-- A two-step return at the translating element forces idempotence. -/
theorem pointed_period_two (h : Equation907 G) (a : G)
    (hc : a ◇ (a ◇ a) = a) : a ◇ a = a := by
  have hs : (a ◇ a) ◇ (a ◇ a) = a ◇ a :=
    left_injective h a ((h a a).symm.trans hc.symm)
  have ht : (a ◇ a) ◇ a = a ◇ a := by
    apply left_injective h a
    calc
      a ◇ ((a ◇ a) ◇ a) = a := by simpa only [hc] using inverse_left_identity h a a
      _ = a ◇ (a ◇ a) := hc.symm
  exact (left_injective h (a ◇ a) (ht.trans hs.symm)).symm

/-- A three-step return at the translating element forces idempotence. -/
theorem pointed_period_three (h : Equation907 G) (a : G)
    (hc : a ◇ (a ◇ (a ◇ a)) = a) : a ◇ a = a := by
  let t := a ◇ (a ◇ a)
  have hta : t ◇ a = a := by
    apply left_injective h a
    simpa only [hc] using inverse_left_identity h a (a ◇ a)
  have hat : a ◇ t = a := hc
  simpa only [hta, hat] using inverse_left_identity h t a

/-- A four-step return at the translating element forces idempotence. -/
theorem pointed_period_four (h : Equation907 G) (a : G)
    (hc : a ◇ (a ◇ (a ◇ (a ◇ a))) = a) : a ◇ a = a := by
  let s := a ◇ a
  let t := a ◇ s
  let u := a ◇ t
  have hau : a ◇ u = a := hc
  have hua : u ◇ a = s := by
    apply left_injective h a
    have hh := inverse_left_identity h a t
    change (a ◇ u) ◇ (u ◇ a) = t at hh
    simpa only [hau] using hh
  have hta : t ◇ a = a := by
    apply left_injective h u
    calc
      u ◇ (t ◇ a) = s := inverse_left_identity h a s
      _ = u ◇ a := hua.symm
  have hsa : s ◇ a = a := by
    apply left_injective h t
    calc
      t ◇ (s ◇ a) = a := inverse_left_identity h a a
      _ = t ◇ a := hta.symm
  have hh := h a u
  simpa only [hua, hau, hsa] using hh.symm

spectrum_assert pointed_period_two complete
spectrum_assert pointed_period_three complete
spectrum_assert pointed_period_four complete
end Spectrum.E907
