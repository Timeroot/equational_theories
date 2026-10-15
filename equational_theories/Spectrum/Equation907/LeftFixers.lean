import equational_theories.Spectrum.Equation907

/-! Left fixers in a finite E907 magma are unique. This is a consequence of
left cancellation, without assuming right cancellation or idempotence. -/
namespace Spectrum.E907
variable {G : Type*} [Magma G] [Finite G]

/-- If `a*x=x`, then applying `L_x` twice to `a` returns `x`. -/
theorem left_fixer_predecessor (h : Equation907 G) {a x : G}
    (ha : a ◇ x = x) : x ◇ (x ◇ a) = x := by
  apply left_injective h a
  simpa only [ha] using (h x a).symm.trans ha.symm

/-- Every point has at most one left fixer. Existence is not asserted. -/
theorem left_fixer_unique (h : Equation907 G) {a b x : G}
    (ha : a ◇ x = x) (hb : b ◇ x = x) : a = b := by
  apply left_injective h x
  apply left_injective h x
  exact (left_fixer_predecessor h ha).trans (left_fixer_predecessor h hb).symm

spectrum_assert left_fixer_predecessor complete
spectrum_assert left_fixer_unique complete
end Spectrum.E907
