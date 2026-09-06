import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import equational_theories.Definability.Linear

/-!
# Five integer models, and the targets integrality refutes

`Definability/LinearZMod.lean` scans the linear magmas over `ZMod m` and `Definability/Linear.lean`
gives the congruence that bounds their clones: a term of `x ◇ y = a * x + b * y` is `α * x + β * y`
with `α + β ≡ 1` modulo any `c` dividing `a + b - 1`. That scan is finished. What it cannot see is
a target whose coefficient system forces `2 * α = 1`, because `2` is a unit in almost every
`ZMod m` — the obstruction is integrality, not a congruence, and only a char-0 model exposes it.

`Definability/LinearInt.lean` is the one such model already on the board, `(ℤ, -x - y)`, aimed at
equations `3272` and `4091`. The targets here are a different family:

* `332`,  `x ◇ y = y ◇ (x ◇ x)`
* `3342`, `x ◇ y = y ◇ (x ◇ (x ◇ x))`
* `3545`, `x ◇ y = y ◇ ((x ◇ x) ◇ x)`
* `4343`, `x ◇ (y ◇ y) = y ◇ (x ◇ x)`
* `3558`, `x ◇ y = y ◇ ((y ◇ y) ◇ x)`

Each of them is satisfied by the constant operation, which is what makes them hard: on a finite
magma the constant operation is usually inside the clone, so no finite certificate reaches them.
Over `ℤ` the coefficient system of each has only the constant solution `α = β = 0` and — for `3342`,
`3545` and `4343` — the one further solution with `α + β = -2`. Both are excluded by the congruence
as soon as `c` divides neither `1` nor `3`, so the refutation needs nothing about the model beyond
its modulus, and one lemma per target serves every model.

The five models are `lin (-1) (-1)` with `c = 3`, `lin (-2) (-2)` and `lin 4 2` with `c = 5`,
`lin (-4) (-2)` with `c = 7`, and `lin (-4) 2` with `c = 3`. Between them they cover the sources
`43`, `492`, `3364`, `4293`, `4321`, `4343` and `4369`.

`Definability/LinearIntModelsCover.lean` reads off the sixteen non-definability facts. Being clone
arguments over an infinite model these refute `TermDefinableFrom` only, and only over all magmas.
-/

open Law Law.MagmaLaw

namespace Magma

/-! ### The targets

For an operation `α * x + β * y` the coefficient equations are the target evaluated at `(1, 0)` and
at `(0, 1)`. Each hypothesis `hc0` / `hc2` says that the congruence class `1 + c * ℤ` misses the
coefficient sum of one of the target's integer solutions. -/

/-- No linear operation over `ℤ` whose coefficient sum is `1` modulo `c` satisfies equation `332`,
`x ◇ y = y ◇ (x ◇ x)`, provided `c` does not divide `1`.

The equations are `α = β * (α + β)` and `β = α`, so `α * (2 * α - 1) = 0`. Integrality kills
`2 * α = 1` and the congruence kills the constant operation. -/
theorem linShift_not_332 {c : ℤ} (hc0 : ∀ g : ℤ, 1 + c * g ≠ 0) (op : ℤ → ℤ → ℤ)
    (hop : LinShift c op) : ¬ @Equation332 ℤ (Magma.mk op) := by
  obtain ⟨a, b, g, hf, hs⟩ := hop
  intro he
  have h1 : a = b * (a + b) := by
    have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have h2 : b = a := by
    have := he 0 1; simp only [Magma.op, hf] at this; linear_combination this
  rw [h2] at h1 hs
  have key : a * (2 * a - 1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp key with h | h
  · exact hc0 g (by linarith)
  · omega

/-- No linear operation over `ℤ` whose coefficient sum is `1` modulo `c` satisfies equation `3342`,
`x ◇ y = y ◇ (x ◇ (x ◇ x))`, provided `c` divides neither `1` nor `3`.

The eliminated equation is `α * ((2 * α - 1) * (α + 1)) = 0`: the middle factor is impossible over
`ℤ`, the outer two give the coefficient sums `0` and `-2`. -/
theorem linShift_not_3342 {c : ℤ} (hc0 : ∀ g : ℤ, 1 + c * g ≠ 0) (hc2 : ∀ g : ℤ, 1 + c * g ≠ -2)
    (op : ℤ → ℤ → ℤ) (hop : LinShift c op) : ¬ @Equation3342 ℤ (Magma.mk op) := by
  obtain ⟨a, b, g, hf, hs⟩ := hop
  intro he
  have h1 : a = b * (a + b * (a + b)) := by
    have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have h2 : b = a := by
    have := he 0 1; simp only [Magma.op, hf] at this; linear_combination this
  rw [h2] at h1 hs
  have key : a * ((2 * a - 1) * (a + 1)) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp key with h | h
  · exact hc0 g (by linarith)
  · rcases mul_eq_zero.mp h with h' | h'
    · omega
    · exact hc2 g (by linarith)

/-- No linear operation over `ℤ` whose coefficient sum is `1` modulo `c` satisfies equation `3545`,
`x ◇ y = y ◇ ((x ◇ x) ◇ x)`, provided `c` divides neither `1` nor `3`. The eliminated equation is
the same as for `3342`. -/
theorem linShift_not_3545 {c : ℤ} (hc0 : ∀ g : ℤ, 1 + c * g ≠ 0) (hc2 : ∀ g : ℤ, 1 + c * g ≠ -2)
    (op : ℤ → ℤ → ℤ) (hop : LinShift c op) : ¬ @Equation3545 ℤ (Magma.mk op) := by
  obtain ⟨a, b, g, hf, hs⟩ := hop
  intro he
  have h1 : a = b * (a * (a + b) + b) := by
    have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have h2 : b = a := by
    have := he 0 1; simp only [Magma.op, hf] at this; linear_combination this
  rw [h2] at h1 hs
  have key : a * ((2 * a - 1) * (a + 1)) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp key with h | h
  · exact hc0 g (by linarith)
  · rcases mul_eq_zero.mp h with h' | h'
    · omega
    · exact hc2 g (by linarith)

/-- No linear operation over `ℤ` whose coefficient sum is `1` modulo `c` satisfies equation `4343`,
`x ◇ (y ◇ y) = y ◇ (x ◇ x)`, provided `c` divides neither `1` nor `3`.

Here both basis instances give the same equation `α = β * (α + β)`, which rearranges to
`(α + β + 1) * (1 - β) = 1`. So `α + β + 1` is a unit and the coefficient sum is `0` or `-2`; the
solutions are the constant operation and `-4 * x + 2 * y`. -/
theorem linShift_not_4343 {c : ℤ} (hc0 : ∀ g : ℤ, 1 + c * g ≠ 0) (hc2 : ∀ g : ℤ, 1 + c * g ≠ -2)
    (op : ℤ → ℤ → ℤ) (hop : LinShift c op) : ¬ @Equation4343 ℤ (Magma.mk op) := by
  obtain ⟨a, b, g, hf, hs⟩ := hop
  intro he
  have h1 : a = b * (a + b) := by
    have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have hkey : (a + b + 1) * (1 - b) = 1 := by linear_combination h1
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hkey) with h | h
  · exact hc0 g (by linarith)
  · exact hc2 g (by linarith)

/-- No linear operation over `ℤ` whose coefficient sum is `1` modulo `c` satisfies equation `3558`,
`x ◇ y = y ◇ ((y ◇ y) ◇ x)`, provided `c` does not divide `1`.

The equations are `α = β ^ 2` and `β = α + α * β * (α + β)`, which eliminate to
`β * (1 - β - β ^ 3 - β ^ 4) = 0`. The second factor makes `β` a unit, and neither `1` nor `-1` is
a root of it, so only the constant operation survives. -/
theorem linShift_not_3558 {c : ℤ} (hc0 : ∀ g : ℤ, 1 + c * g ≠ 0) (op : ℤ → ℤ → ℤ)
    (hop : LinShift c op) : ¬ @Equation3558 ℤ (Magma.mk op) := by
  obtain ⟨a, b, g, hf, hs⟩ := hop
  intro he
  have h1 : a = b * b := by
    have := he 1 0; simp only [Magma.op, hf] at this; linear_combination this
  have h2 : b = a + a * b * (a + b) := by
    have := he 0 1; simp only [Magma.op, hf] at this; linear_combination this
  rw [h1] at h2 hs
  have key : b * (1 - b - b ^ 3 - b ^ 4) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp key with h | h
  · subst h; exact hc0 g (by linarith)
  · have hfac : b * (1 + b ^ 2 + b ^ 3) = 1 := by linear_combination -h
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hfac) with h' | h' <;>
      subst h' <;> norm_num at h

end Magma

/-! ### The models

Each model is one `Satisfies` list and one partially applied `Magma.not_termDefinableFrom_of_lin`.
The divisibility witness `e` in `a + b = 1 + c * e` is written out; nothing here is decidable. -/

/-- The sources satisfied by `-x - y` over `ℤ` that this file needs. -/
theorem liA_sat : Satisfies (Magma.lin (-1 : ℤ) (-1)) [492, 3364] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.lin_op]
  all_goals ring

/-- The certificate of `-x - y` over `ℤ`: its coefficient sum is `1` modulo `3`. -/
theorem liA_cert {L L' : Law.MagmaLaw ℕ}
    (hM : @satisfies _ ℤ (Magma.lin (-1 : ℤ) (-1)) L')
    (hL : ∀ op : ℤ → ℤ → ℤ, Magma.LinShift (3 : ℤ) op → ¬ @satisfies _ ℤ (Magma.mk op) L) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_invariant _ hM
    (Magma.lin_isCloneInvariant (-1 : ℤ) (-1) 3 (-1) (by norm_num)) hL

/-- The source satisfied by `-2 * x - 2 * y` over `ℤ` that this file needs. -/
theorem liB_sat : Satisfies (Magma.lin (-2 : ℤ) (-2)) [43] := by
  all_goals repeat intro _
  all_goals simp only [Magma.lin_op]
  all_goals ring

/-- The certificate of `-2 * x - 2 * y` over `ℤ`: its coefficient sum is `1` modulo `5`. -/
theorem liB_cert {L L' : Law.MagmaLaw ℕ}
    (hM : @satisfies _ ℤ (Magma.lin (-2 : ℤ) (-2)) L')
    (hL : ∀ op : ℤ → ℤ → ℤ, Magma.LinShift (5 : ℤ) op → ¬ @satisfies _ ℤ (Magma.mk op) L) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_invariant _ hM
    (Magma.lin_isCloneInvariant (-2 : ℤ) (-2) 5 (-1) (by norm_num)) hL

/-- The sources satisfied by `4 * x + 2 * y` over `ℤ` that this file needs. -/
theorem liC_sat : Satisfies (Magma.lin (4 : ℤ) 2) [4321, 4369] := by
  repeat' apply And.intro
  all_goals repeat intro _
  all_goals simp only [Magma.lin_op]
  all_goals ring

/-- The certificate of `4 * x + 2 * y` over `ℤ`: its coefficient sum is `1` modulo `5`. -/
theorem liC_cert {L L' : Law.MagmaLaw ℕ}
    (hM : @satisfies _ ℤ (Magma.lin (4 : ℤ) 2) L')
    (hL : ∀ op : ℤ → ℤ → ℤ, Magma.LinShift (5 : ℤ) op → ¬ @satisfies _ ℤ (Magma.mk op) L) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_invariant _ hM
    (Magma.lin_isCloneInvariant (4 : ℤ) 2 5 1 (by norm_num)) hL

/-- The source satisfied by `-4 * x - 2 * y` over `ℤ` that this file needs. -/
theorem liD_sat : Satisfies (Magma.lin (-4 : ℤ) (-2)) [4293] := by
  all_goals repeat intro _
  all_goals simp only [Magma.lin_op]
  all_goals ring

/-- The certificate of `-4 * x - 2 * y` over `ℤ`: its coefficient sum is `1` modulo `7`. -/
theorem liD_cert {L L' : Law.MagmaLaw ℕ}
    (hM : @satisfies _ ℤ (Magma.lin (-4 : ℤ) (-2)) L')
    (hL : ∀ op : ℤ → ℤ → ℤ, Magma.LinShift (7 : ℤ) op → ¬ @satisfies _ ℤ (Magma.mk op) L) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_invariant _ hM
    (Magma.lin_isCloneInvariant (-4 : ℤ) (-2) 7 (-1) (by norm_num)) hL

/-- The source satisfied by `-4 * x + 2 * y` over `ℤ` that this file needs. It is the one model
whose own operation is the second solution of equation `4343`'s coefficient system. -/
theorem liE_sat : Satisfies (Magma.lin (-4 : ℤ) 2) [4343] := by
  all_goals repeat intro _
  all_goals simp only [Magma.lin_op]
  all_goals ring

/-- The certificate of `-4 * x + 2 * y` over `ℤ`: its coefficient sum is `1` modulo `3`. -/
theorem liE_cert {L L' : Law.MagmaLaw ℕ}
    (hM : @satisfies _ ℤ (Magma.lin (-4 : ℤ) 2) L')
    (hL : ∀ op : ℤ → ℤ → ℤ, Magma.LinShift (3 : ℤ) op → ¬ @satisfies _ ℤ (Magma.mk op) L) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_invariant _ hM
    (Magma.lin_isCloneInvariant (-4 : ℤ) 2 3 (-1) (by norm_num)) hL
