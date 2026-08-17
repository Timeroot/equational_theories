import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import equational_theories.Definability.Invariant
import equational_theories.Definability.CertSyntax
import equational_theories.Equations.All

/-!
# The integer certificate `(ℤ, x ◇ y = -x - y)`

Every certificate elsewhere in `Definability/` is finite, and for the two heaviest targets on the
board — equation `3272`, `x ◇ x = y ◇ (x ◇ (y ◇ y))`, and its dual `4091` — the finite ones all
fail. They fail for a structural reason: both sides of the target are compound, so the constant
operation satisfies it, and on a finite magma the constant operation is very often available inside
the clone. `(ℤ, -x - y)` is the smallest model where it is not.

The clone of `(ℤ, a * x + b * y)` consists of linear operations `α * x + β * y`, and the two
projections have `α + β = 1` while a composite has `α + β = a * (α₁ + β₁) + b * (α₂ + β₂)`. So with
`a = b = -1` the sum of the coefficients of any term is congruent to `1` modulo `3`: it starts at
`1` and each composition sends `s₁, s₂ ↦ -s₁ - s₂ ≡ -2 ≡ 1`. That is the invariant `Magma.Linear3`,
and it excludes the constant operation `α = β = 0`, which is the only thing that would have
satisfied either target.

Nothing here is decidable and none of it is generated: the model is infinite, so the refutations
are algebra. `Definability/LinearIntCover.lean` assembles them into the `184` non-definability
facts they give on the open board.

Being an infinite model this refutes term-definability over *all* magmas only. It says nothing
about the finite-magma variant, and — like every clone argument — nothing about first-order
definability.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The magma `x ◇ y = -x - y` on `ℤ`. -/
@[implicit_reducible]
def negInt : Magma ℤ := Magma.mk fun x y ↦ -x - y

@[simp] theorem negInt_op (x y : ℤ) : negInt.op x y = -x - y := rfl

/-- The clone invariant of `Magma.negInt`: a linear operation whose coefficients sum to `1` mod
`3`. The congruence is what rules out the constant operation `α = β = 0`. -/
def Linear3 (f : ℤ → ℤ → ℤ) : Prop :=
  ∃ a b : ℤ, (∀ x y, f x y = a * x + b * y) ∧ (a + b) % 3 = 1

theorem negInt_isCloneInvariant : negInt.IsCloneInvariant Linear3 where
  fst := ⟨1, 0, fun x y ↦ by ring, by decide⟩
  snd := ⟨0, 1, fun x y ↦ by ring, by decide⟩
  comp := by
    rintro f g ⟨a₁, b₁, hf, hs₁⟩ ⟨a₂, b₂, hg, hs₂⟩
    refine ⟨-a₁ - a₂, -b₁ - b₂, fun x y ↦ ?_, by omega⟩
    show negInt.op (f x y) (g x y) = _
    rw [negInt_op, hf, hg]; ring

end Magma

/-! ### The two targets

For an operation `α * x + β * y` the target's two coefficient equations are read off by evaluating
at `(x, y) = (1, 0)` and `(0, 1)`. Eliminating between them leaves a single factored equation whose
only integer solutions are the constant operation and one other pair; the congruence kills the
first and integrality kills the second.
-/

namespace Magma

/-- No linear operation with coefficient sum `1` mod `3` satisfies equation `3272`,
`x ◇ x = y ◇ (x ◇ (y ◇ y))`.

The coefficient equations are `α + β = α * β` and `0 = α + β ^ 2 * (α + β)`; together they give
`α * (1 + β ^ 3) = 0`. If `α = 0` then `β = 0` and the sum is `0`, not `1` mod `3`; otherwise
`β = -1`, and the first equation becomes `2 * α = 1`, which has no integer solution. -/
theorem negInt_refutes_3272 (op : ℤ → ℤ → ℤ) (hop : Linear3 op) :
    ¬ @Equation3272 ℤ (Magma.mk op) := by
  obtain ⟨a, b, hf, hm⟩ := hop
  intro he
  have h1 : a + b = a * b := by have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have h2 : (0 : ℤ) = a + b ^ 2 * (a + b) := by
    have := he 0 1; simp only [Magma.op, hf] at this; linear_combination this
  have key : a * (1 + b ^ 3) = 0 := by linear_combination (-b ^ 2) * h1 - h2
  rcases mul_eq_zero.mp key with ha | hb
  · subst ha
    have hb0 : b = 0 := by linear_combination h1
    subst hb0; omega
  · have hfac : (1 + b) * (1 - b + b ^ 2) = 0 := by linear_combination hb
    have hpos : 0 < 1 - b + b ^ 2 := by nlinarith [sq_nonneg (2 * b - 1)]
    have hb1 : b = -1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · omega
    subst hb1
    have : 2 * a = 1 := by linear_combination h1
    omega

/-- No linear operation with coefficient sum `1` mod `3` satisfies equation `4091`,
`x ◇ x = ((y ◇ y) ◇ x) ◇ y`. This is the dual of `negInt_refutes_3272` and the proof is the mirror
image: the eliminated equation is `β * (1 + α ^ 3) = 0`. -/
theorem negInt_refutes_4091 (op : ℤ → ℤ → ℤ) (hop : Linear3 op) :
    ¬ @Equation4091 ℤ (Magma.mk op) := by
  obtain ⟨a, b, hf, hm⟩ := hop
  intro he
  have h1 : a + b = a * b := by have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have h2 : (0 : ℤ) = a ^ 2 * (a + b) + b := by
    have := he 0 1; simp only [Magma.op, hf] at this; linear_combination this
  have key : b * (1 + a ^ 3) = 0 := by linear_combination (-a ^ 2) * h1 - h2
  rcases mul_eq_zero.mp key with hb | ha
  · subst hb
    have ha0 : a = 0 := by linear_combination h1
    subst ha0; omega
  · have hfac : (1 + a) * (1 - a + a ^ 2) = 0 := by linear_combination ha
    have hpos : 0 < 1 - a + a ^ 2 := by nlinarith [sq_nonneg (2 * a - 1)]
    have ha1 : a = -1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · omega
    subst ha1
    have : 2 * b = 1 := by linear_combination h1
    omega

end Magma

/-! ### The sources

The equations `Magma.negInt` satisfies, and so may be used as the *source* of a certificate. Only
the implication-minimal ones that contribute an open-board cell are listed. Each is an identity
between two linear forms in the free variables, so `ring` closes it. -/

/-- Part 1 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_0 :
    Satisfies Magma.negInt [
      14, 29, 477, 489, 492, 522,
      572, 680, 684, 692, 711, 725
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 2 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_1 :
    Satisfies Magma.negInt [
      746, 759, 1073, 1152, 1155, 1165,
      1181, 1276, 1293, 1304, 1320, 1358
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 3 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_2 :
    Satisfies Magma.negInt [
      1492, 1504, 1507, 1519, 1558, 1561,
      1695, 1699, 1707, 1932, 1943, 1977
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 4 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_3 :
    Satisfies Magma.negInt [
      2128, 2135, 2167, 2170, 2180, 2196,
      2291, 2335, 2349, 2373, 2399, 2494
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 5 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_4 :
    Satisfies Magma.negInt [
      2519, 2522, 2573, 2576, 2917, 2925,
      2944, 2947, 2958, 2979, 2992, 3120
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 6 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_5 :
    Satisfies Magma.negInt [
      3131, 3150, 3195, 3211, 3364, 3370,
      3417, 3472, 3553, 3567, 3588, 3601
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 7 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_6 :
    Satisfies Magma.negInt [
      3878, 3994, 4007, 4013, 4026, 4162,
      4182, 4216, 4273, 4305, 4332, 4386
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring

/-- Part 8 of the source list satisfied by `Magma.negInt`. -/
theorem negInt_satisfies_7 :
    Satisfies Magma.negInt [
      4413, 4421, 4446, 4450, 4458, 4588,
      4640, 4647
    ] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.negInt_op]
  all_goals ring
