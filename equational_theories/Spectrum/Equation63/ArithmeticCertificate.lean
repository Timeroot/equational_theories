import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.GCD.Basic

/-! A compact certificate for seven-group gluing. A set bit of `B` records an
available group size. For a fixed admissible `q`, one shift records every order
`7*q+r` with `r ≤ q` available, rather than checking these orders individually.
All computations in the concrete certificate are checked by kernel reduction. -/
namespace Spectrum.E63.ArithmeticCertificate

def Decomposes (B n : ℕ) : Prop :=
  ∃ q r, 0 < q ∧ q.Coprime 60 ∧ r ≤ q ∧
    B.testBit q = true ∧ B.testBit r = true ∧ 7*q+r = n

/-- Restrict the remainder bitmap to `[0,q]`, then translate it by `7*q`. -/
def image (B q : ℕ) : ℕ :=
  if 0 < q ∧ q.Coprime 60 ∧ B.testBit q = true then
    (B % 2^(q+1)) <<< (7*q)
  else 0

theorem image_sound {B q n : ℕ} (h : (image B q).testBit n = true) :
    Decomposes B n := by
  unfold image at h
  split at h
  · rename_i hq
    simp only [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hle, hlt, hbit⟩ := h
    exact ⟨q, n-7*q, hq.1, hq.2.1, by omega, hq.2.2, hbit, by omega⟩
  · simp at h

/-- The union of the orders supplied by the listed group sizes. -/
def cover (B : ℕ) (groups : List ℕ) : ℕ :=
  groups.foldr (fun q rest => image B q ||| rest) 0

theorem cover_sound {B n : ℕ} {groups : List ℕ}
    (h : (cover B groups).testBit n = true) : Decomposes B n := by
  induction groups with
  | nil => simp [cover] at h
  | cons q qs ih =>
    change (image B q ||| cover B qs).testBit n = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    exact h.elim image_sound ih

/-- One integer equality checks every bit in a complete interval. -/
theorem interval_covered {B lo len n : ℕ}
    (h : (B >>> lo) % 2^len = 2^len-1)
    (hlo : lo ≤ n) (hhi : n < lo+len) : B.testBit n = true := by
  have hb := congrArg (fun x => x.testBit (n-lo)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight, show n-lo < len by omega, decide_true,
    Bool.true_and] at hb
  simpa only [show lo+(n-lo) = n by omega] using hb

theorem bit_lt {B bound n : ℕ} (hB : B % 2^bound = B)
    (hn : B.testBit n = true) : n < bound := by
  have h := congrArg (fun x => x.testBit n) hB
  simp only [Nat.testBit_mod_two_pow, hn, Bool.and_true, decide_eq_true_eq] at h
  exact h

end Spectrum.E63.ArithmeticCertificate
