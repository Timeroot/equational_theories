import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Ring

/-!
# The arithmetic of exact degree halving

The spectrum argument only needs the following elementary descent: a positive
minimum degree is attained, and every larger degree is twice another degree.
Strong induction then makes every degree a power-of-two multiple of the minimum.
Multiplying the minimum and maximum gives a square times a power of two, hence
either a square or twice a square.

These lemmas do not depend on magmas or on finiteness of the degree family.
-/

namespace WeakCentralGroupoid

/-- Exact halving above a positive lower bound makes every value dyadic over
that bound. In particular, the lower bound is attained whenever `α` is nonempty. -/
theorem eq_min_mul_pow_two {α : Type*} (d : α → ℕ) (r : ℕ) (hr : 0 < r)
    (hmin : ∀ a, r ≤ d a)
    (hhalf : ∀ a, r < d a → ∃ b, d a = 2 * d b) (a : α) :
    ∃ k, d a = r * 2 ^ k := by
  have aux : ∀ n : ℕ, ∀ a : α, d a = n → ∃ k, d a = r * 2 ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases heq : d a = r
      · exact ⟨0, by simpa using heq⟩
      · have hgt : r < d a := lt_of_le_of_ne (hmin a) (Ne.symm heq)
        obtain ⟨b, hb⟩ := hhalf a hgt
        have hlt : d b < n := by have := hmin b; omega
        obtain ⟨k, hk⟩ := ih (d b) hlt b rfl
        refine ⟨k + 1, ?_⟩
        rw [hb, hk, pow_succ]
        ring
  exact aux (d a) a rfl

/-- Once a dyadic value occurs, exact halving realizes every lower dyadic value.
No maximality of the given value is needed. -/
theorem exists_eq_min_mul_pow_two {α : Type*} (d : α → ℕ) (r : ℕ) (hr : 0 < r)
    (hhalf : ∀ a, r < d a → ∃ b, d a = 2 * d b)
    {m : ℕ} (a : α) (ha : d a = r * 2 ^ m) {k : ℕ} (hkm : k ≤ m) :
    ∃ b, d b = r * 2 ^ k := by
  induction m generalizing a k with
  | zero =>
    have hk : k = 0 := by omega
    exact ⟨a, hk ▸ ha⟩
  | succ m ih =>
    by_cases hk : k = m + 1
    · exact ⟨a, hk ▸ ha⟩
    · have hdouble : d a = 2 * (r * 2 ^ m) := by
        rw [ha, pow_succ]
        ring
      have hle : r ≤ r * 2 ^ m :=
        Nat.le_mul_of_pos_right r (Nat.pow_pos (by decide))
      have hgt : r < d a := by omega
      obtain ⟨b, hb⟩ := hhalf a hgt
      have hdb : d b = r * 2 ^ m := by omega
      exact ih b hdb (by omega)

/-- A square times a power of two is a square or twice a square. -/
theorem square_or_twice_square_of_dyadic {n r k : ℕ}
    (h : n = r ^ 2 * 2 ^ k) : ∃ q, n = q ^ 2 ∨ n = 2 * q ^ 2 := by
  have hk : ∃ m : ℕ, k = m * 2 ∨ k = m * 2 + 1 := by
    exact ⟨k / 2, by omega⟩
  obtain ⟨m, rfl | rfl⟩ := hk
  · exact ⟨r * 2 ^ m, Or.inl (by simpa only [mul_pow, pow_mul] using h)⟩
  · refine ⟨r * 2 ^ m, Or.inr ?_⟩
    rw [h, pow_succ (2 : ℕ) (m * 2), pow_mul, mul_pow]
    ring

/-- info: 'WeakCentralGroupoid.eq_min_mul_pow_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eq_min_mul_pow_two

/-- info: 'WeakCentralGroupoid.exists_eq_min_mul_pow_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_eq_min_mul_pow_two

/-- info: 'WeakCentralGroupoid.square_or_twice_square_of_dyadic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms square_or_twice_square_of_dyadic

end WeakCentralGroupoid
