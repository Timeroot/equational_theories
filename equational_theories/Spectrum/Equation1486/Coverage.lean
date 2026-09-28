import Mathlib.Tactic

/-!+# Arithmetic coverage for the E1486 matching construction

The matching construction supplies all orders in the integer interval
`[n² + 2, n² + 4n - 8]`, for `n ≥ 5`.  These intervals cover every
integer at least 27.  This file isolates that elementary arithmetic from
the construction of the magmas.
-/

namespace Spectrum.E1486

/-- The intervals supplied by the matching construction cover every order
at least 27.  The upper bound is written without natural-number subtraction. -/
theorem exists_matching_interval (N : ℕ) (hN : 27 ≤ N) :
    ∃ n : ℕ, 5 ≤ n ∧ n ^ 2 + 2 ≤ N ∧ N + 8 ≤ n ^ 2 + 4 * n := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hbase : N = 27
    · subst N
      exact ⟨5, by norm_num, by norm_num, by norm_num⟩
    have hprev : 27 ≤ N - 1 := by omega
    have hsucc : N - 1 + 1 = N := by omega
    obtain ⟨n, hn, hlo, hhi⟩ := ih (N - 1) (by omega) hprev
    by_cases hfit : N + 8 ≤ n ^ 2 + 4 * n
    · exact ⟨n, hn, by omega, hfit⟩
    · refine ⟨n + 1, by omega, ?_, ?_⟩ <;> nlinarith

/-- A construction on each matching interval gives a cofinite family with
the explicit bound 27. -/
theorem atLeast27_of_matching_intervals (P : ℕ → Prop)
    (h : ∀ n : ℕ, 5 ≤ n → ∀ N : ℕ,
      n ^ 2 + 2 ≤ N → N + 8 ≤ n ^ 2 + 4 * n → P N)
    (N : ℕ) (hN : 27 ≤ N) : P N := by
  obtain ⟨n, hn, hlo, hhi⟩ := exists_matching_interval N hN
  exact h n hn N hlo hhi

end Spectrum.E1486
