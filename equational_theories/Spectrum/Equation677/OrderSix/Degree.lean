import Mathlib.Dynamics.PeriodicPts.Lemmas
import equational_theories.Spectrum.Equation677.OrderSix.Basic

namespace Spectrum.E677.OrderSix
universe u
open scoped Spectrum.E677.OrderSix
local infixl:70 " * " => Magma.op
/-! ## The degree

For a fixed $a$, the points $L_a^n(a)$ run around the cycle of the permutation $L_a$ through
$a$; its length is the degree of $a$. The degree predicate records the least positive return time. Its existence
uses Mathlib's minimal-period and finite-cardinality theorems. -/

section Orbit

variable {M : Type u} [Magma M]

/-- `leftApplyMul a b n` is $L_b^n(a) = b \diamond (b \diamond \cdots (b \diamond a))$. -/
def leftApplyMul (a b : M) : Nat → M
  | 0 => a
  | n + 1 => b * leftApplyMul a b n

/-- **The degree of `a` is `n`**: $n$ is the least positive exponent with $L_a^n(a) = a$. -/
def HasDeg (a : M) (n : Nat) : Prop :=
  0 < n ∧ leftApplyMul a a n = a ∧ ∀ k, 0 < k → k < n → leftApplyMul a a k ≠ a

theorem leftApplyMul_eq_iterate (a b : M) (n : Nat) :
    leftApplyMul a b n = (fun x => b * x)^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [leftApplyMul, Function.iterate_succ_apply', ih]

end Orbit

section Degree

variable {M : Type u} [Magma M] [Fact (Equation677 M)] [Finite M]

/-- $L_a$ cancels along the orbit: $L_a^{i+k}(a) = L_a^{j+k}(a)$ forces
$L_a^i(a) = L_a^j(a)$. -/
theorem leftApplyMul_cancel (a : M) : ∀ k i j : Nat,
    leftApplyMul a a (i + k) = leftApplyMul a a (j + k) → leftApplyMul a a i = leftApplyMul a a j
  | 0, _, _, h => h
  | k + 1, i, j, h => leftApplyMul_cancel a k i j (mul_left_cancel h)

/-- A repetition $L_a^i(a) = L_a^j(a)$ with $i \le j$ is a return $L_a^{j-i}(a) = a$. -/
theorem leftApplyMul_sub_eq_self (a : M) {i j : Nat} (hij : i ≤ j)
    (h : leftApplyMul a a i = leftApplyMul a a j) : leftApplyMul a a (j - i) = a :=
  (leftApplyMul_cancel a i 0 (j - i) (by rw [Nat.zero_add, Nat.sub_add_cancel hij]; exact h)).symm

/-- **One turn of the orbit visits distinct points**: if $a$ has degree $n$, the points
$L_a^k(a)$ for $k < n$ are pairwise distinct. -/
theorem HasDeg.ne {a : M} {n : Nat} (h : HasDeg a n) {i j : Nat} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : leftApplyMul a a i ≠ leftApplyMul a a j := by
  intro heq
  rcases (by omega : i < j ∨ j < i) with hlt | hlt
  · exact h.2.2 (j - i) (by omega) (by omega)
      (leftApplyMul_sub_eq_self a (Nat.le_of_lt hlt) heq)
  · exact h.2.2 (i - j) (by omega) (by omega)
      (leftApplyMul_sub_eq_self a (Nat.le_of_lt hlt) heq.symm)

/-- **Every element has a degree, at most $|M|$.** Among the $|M| + 1$ points
$a, L_a(a), \dots, L_a^{|M|}(a)$ two coincide, which by cancellation is a return to $a$; the
degree is the least return time. -/
theorem exists_hasDeg (a : M) : ∃ n, n ≤ Nat.card M ∧ HasDeg a n := by
  classical
  letI := Fintype.ofFinite M
  let f : M → M := fun x => a * x
  have hi : Function.Injective f := Eq677.eq677_leftMul_inj (Fact.out : Equation677 M) a
  refine ⟨Function.minimalPeriod f a, ?_,
    Function.minimalPeriod_pos_of_mem_periodicPts (hi.mem_periodicPts a), ?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card] using (Function.minimalPeriod_le_card (f := f) (x := a))
  · rw [leftApplyMul_eq_iterate]
    exact Function.iterate_minimalPeriod
  · intro k hk hkn he
    rw [leftApplyMul_eq_iterate] at he
    exact (not_le_of_gt hkn) (Function.IsPeriodicPt.minimalPeriod_le hk he)

/-- **No element has degree $2$**: $a \diamond (a \diamond a) = a$ forces idempotence, which is
a return at time $1$. -/
theorem not_hasDeg_two (a : M) : ¬ HasDeg a 2 := fun h =>
  h.2.2 1 (by decide) (by decide) (isIdempotentElem_of_mul_sq (a := a) h.2.1)

/-- **No element has degree $3$.** -/
theorem not_hasDeg_three (a : M) : ¬ HasDeg a 3 := fun h =>
  h.2.2 1 (by decide) (by decide) (isIdempotentElem_of_mul_mul_sq (a := a) h.2.1)

/-- **An element satisfying Equation 255 does not have degree $4$**: $L_a^4(a) = a$ says
$a \diamond (a \diamond a) = (a \diamond a) \diamond a$. -/
theorem not_hasDeg_four_of_eq255At {a : M} (h255 : Eq255At a) : ¬ HasDeg a 4 := fun h => by
  have h₁ : a / a = a * (a * (a * a)) := div_eq_iff_mul_eq.mpr h.2.1
  rw [div_def] at h₁
  exact h.2.2 1 (by decide) (by decide)
    (isIdempotentElem_of_mul_sq_eq_sq_mul h255 (mul_left_cancel h₁).symm)

/-- **An element satisfying Equation 255 does not have degree $5$**: $L_a^5(a) = a$ says
$a \diamond (a \diamond (a \diamond a)) = (a \diamond a) \diamond a$. -/
theorem not_hasDeg_five_of_eq255At {a : M} (h255 : Eq255At a) : ¬ HasDeg a 5 := fun h => by
  have h₁ : a / a = a * (a * (a * (a * a))) := div_eq_iff_mul_eq.mpr h.2.1
  rw [div_def] at h₁
  exact h.2.2 1 (by decide) (by decide)
    (isIdempotentElem_of_mul_mul_sq_eq_cube h255 (mul_left_cancel h₁).symm)

end Degree


end Spectrum.E677.OrderSix
