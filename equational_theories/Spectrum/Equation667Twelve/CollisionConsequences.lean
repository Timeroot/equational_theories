import equational_theories.Spectrum.Equation667Twelve.Collisions

/-! Reuse the small collision exclusions before checking the prescribed-row
cases. The hypotheses are deliberately just the two collision refutations,
so none of these deductions depend on the final order-twelve exclusion. -/
namespace Spectrum.E667.Twelve
open RightIdentityTwelve (Holds)

/-- Once four distinct points are excluded, the square of a collision target
is either one of its two preimages or the target itself. -/
theorem collision_target_square (hn : fourFormula.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (a b c : Fin 12) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : f a a = c) (hb : f b b = c) :
    f c c = a ∨ f c c = b ∨ f c c = c := by
  by_contra! hn'
  exact no_four hn f h a b c (f c c) hab hac hn'.1.symm hbc hn'.2.1.symm
    hn'.2.2.symm ha hb rfl

/-- After both non-idempotent collision patterns have been excluded, every
repeated value of the square map is idempotent. This is a derived constraint
on order-twelve models, not an assertion about E667 magmas of every order. -/
theorem collision_target_idempotent (hthree : threeFormula.Unsat) (hfour : fourFormula.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (a b c : Fin 12) (hab : a ≠ b) (ha : f a a = c) (hb : f b b = c) :
    f c c = c := by
  by_cases hac : a = c
  · simpa [hac] using ha
  by_cases hbc : b = c
  · simpa [hbc] using hb
  rcases collision_target_square hfour f h a b c hab hac hbc ha hb with hc | hc | hc
  · exact (no_three hthree f h a b c hab hac hbc ha hb hc).elim
  · exact (no_three hthree f h b a c hab.symm hbc hac hb ha hc).elim
  · exact hc

spectrum_assert collision_target_square complete
spectrum_assert collision_target_idempotent complete
end Spectrum.E667.Twelve
