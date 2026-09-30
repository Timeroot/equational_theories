import equational_theories.Spectrum.Equation677.EffectiveTail.Truncation

/-! Soundness of the packed construction certificates and the final arithmetic
induction. Ported from PR #6; all model predicates now use `Law677.HasModel`.
The accumulator evaluation barriers are retained for kernel checking. -/
namespace Spectrum.E677.EffectiveTail
open Law Law.MagmaLaw
noncomputable section

namespace OrderBitmap

/-! ## Bitmaps of orders -/

/-- A bitmap is **sound** when each of its set bits is the size of a model. -/
def Sound (B : Nat) : Prop := ∀ n, B.testBit n = true → Law677.HasModel n

theorem Sound.or {A B : Nat} (hA : Sound A) (hB : Sound B) : Sound (A ||| B) := by
  intro n h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h.elim (hA n) (hB n)

theorem sound_single {n : Nat} (h : Law677.HasModel n) : Sound (1 <<< n) := by
  intro m hm
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hm
  exact hm ▸ h

/-- **A list of orders that all carry models** gives a sound bitmap. -/
theorem sound_foldr {l : List Nat} (h : ∀ n ∈ l, Law677.HasModel n) :
    Sound (l.foldr (fun n B => B ||| 1 <<< n) 0) := by
  induction l with
  | nil => intro n hn; simp at hn
  | cons n l ih =>
    simp only [List.foldr_cons]
    exact (ih fun m hm => h m (List.Mem.tail _ hm)).or (sound_single (h n (List.Mem.head _)))

/-- Evaluate `a` and continue with it. The test is decided by evaluating `a`, so in a kernel
reduction `forceThen a k` evaluates `a` before `k` runs; the loops below use it to keep their
accumulators evaluated. -/
def forceThen (a : Nat) (k : Nat → Nat) : Nat := if a == 0 then k 0 else k a

theorem forceThen_eq (a : Nat) (k : Nat → Nat) : forceThen a k = k a := by
  unfold forceThen
  split
  · rename_i h
    rw [beq_iff_eq] at h
    rw [h]
  · rfl

/-! ### Bitmaps read relative to a base point -/

/-- A bitmap read relative to `a` is sound when each set bit `i` is the size `a + i` of a
model. -/
def WSound (a A : Nat) : Prop := ∀ i, A.testBit i = true → Law677.HasModel (a + i)

theorem WSound.or {a A B : Nat} (hA : WSound a A) (hB : WSound a B) : WSound a (A ||| B) := by
  intro n h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h.elim (hA n) (hB n)

theorem wsound_zero (a : Nat) : WSound a 0 := fun i h => by simp at h

theorem wsound_single {a n : Nat} (h : Law677.HasModel n) (han : a ≤ n) : WSound a (1 <<< (n - a)) := by
  intro i hi
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hi
  rwa [show a + i = n by omega]

theorem Sound.wsound_shiftRight {B : Nat} (hB : Sound B) (a L : Nat) :
    WSound a ((B >>> a) % 2 ^ L) := by
  intro i hi
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_eq_true] at hi
  exact hB _ hi.2

/-! ### Packed instructions -/

/-- **The two-group truncation `(q, s)`, read relative to `a`.** Let `hq` be the bits of `P`
up to `q`. If `q` is coprime to `P79`, `s ≤ q`, and the orders `q` and `s` are recorded, the
result records `79 q + s + r` (at position `79 q + s + r - a`) for every recorded `r ≤ q`;
otherwise it is empty. -/
def truncImage (P a q s : Nat) : Nat :=
  let hq := P % 2 ^ (q + 1)
  if Nat.gcd q P79 == 1 && decide (s ≤ q) && hq.testBit q && hq.testBit s then
    if a ≤ 79 * q + s then hq <<< (79 * q + s - a) else hq >>> (a - (79 * q + s))
  else 0

theorem wsound_truncImage {P : Nat} (hP : Sound P) (a q s : Nat) :
    WSound a (truncImage P a q s) := by
  intro i hi
  unfold truncImage at hi
  dsimp only at hi
  by_cases ht : (Nat.gcd q P79 == 1 && decide (s ≤ q) && (P % 2 ^ (q + 1)).testBit q &&
      (P % 2 ^ (q + 1)).testBit s) = true
  · rw [if_pos ht] at hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Nat.testBit_mod_two_pow,
      show q < q + 1 by omega, decide_true, Bool.true_and] at ht
    obtain ⟨⟨⟨hg, hsq⟩, hq⟩, hs⟩ := ht
    have hs' : P.testBit s = true := by
      simpa [show s < q + 1 by omega] using hs
    by_cases hw : a ≤ 79 * q + s
    · rw [if_pos hw] at hi
      simp only [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Bool.and_eq_true,
        decide_eq_true_eq] at hi
      obtain ⟨_, hlt, hbit⟩ := hi
      have := hasModel_trunc hg hsq (by omega : i - (79 * q + s - a) ≤ q) (hP q hq) (hP s hs')
        (hP _ hbit)
      rwa [show 79 * q + s + (i - (79 * q + s - a)) = a + i by omega] at this
    · rw [if_neg hw] at hi
      simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Bool.and_eq_true,
        decide_eq_true_eq] at hi
      obtain ⟨hlt, hbit⟩ := hi
      have := hasModel_trunc hg hsq (by omega : a - (79 * q + s) + i ≤ q) (hP q hq) (hP s hs')
        (hP _ hbit)
      rwa [show 79 * q + s + (a - (79 * q + s) + i) = a + i by omega] at this
  · rw [if_neg ht] at hi
    simp at hi

/-- **One packed instruction, read from `P` and placed relative to `a`.** The low three bits
are a tag and three 18-bit fields `x`, `y`, `z` follow. Tag `0`: the affine certificate
`(m, a, b) = (x, y, z)`. Tag `1`: the product of the recorded orders `x` and `y`. Tag `2`: the
two-group truncation `(q, s) = (x, y)`. Anything else, or a failed side condition, gives the
empty bitmap; so does an affine certificate or a product whose order is below `a`, and of a
truncation only the orders from `a` on are kept. -/
def opImage (P a op : Nat) : Nat :=
  let t := op % 8
  let x := (op >>> 3) % 2 ^ 18
  let y := (op >>> 21) % 2 ^ 18
  let z := (op >>> 39) % 2 ^ 18
  if t == 0 then (if affineOK x y z && decide (a ≤ x) then 1 <<< (x - a) else 0)
  else if t == 1 then
    (if P.testBit x && P.testBit y && decide (a ≤ x * y) then 1 <<< (x * y - a) else 0)
  else if t == 2 then truncImage P a x y
  else 0

theorem wsound_opImage {P : Nat} (hP : Sound P) (a op : Nat) : WSound a (opImage P a op) := by
  unfold opImage
  dsimp only
  split
  · split
    · rename_i _ ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
      exact wsound_single (hasModel_of_affineOK ha.1) ha.2
    · exact wsound_zero a
  · split
    · split
      · rename_i _ _ hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        exact wsound_single ((hP _ hp.1.1).mul (hP _ hp.1.2)) hp.2
      · exact wsound_zero a
    · split
      · exact wsound_truncImage hP a _ _
      · exact wsound_zero a

/-- **Accumulate the images of a list of instructions**, read from `P` and placed relative to
`a`, keeping the accumulator evaluated between instructions. -/
def blockAcc (P a : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun op _ ih acc => forceThen acc fun acc => ih (acc ||| opImage P a op))

theorem wsound_blockAcc {P : Nat} (hP : Sound P) (a : Nat) :
    ∀ (ops : List Nat) {acc : Nat}, WSound a acc → WSound a (blockAcc P a ops acc)
  | [], _, h => h
  | op :: ops, acc, h => by
    change WSound a (forceThen acc fun acc => blockAcc P a ops (acc ||| opImage P a op))
    rw [forceThen_eq]
    exact wsound_blockAcc hP a ops (h.or (wsound_opImage hP a op))

/-! ### Two kinds of check -/

/-- **A block of a bitmap is produced from below.** The bits of `H` in `[a, a + L)` all
appear among the bits of `seeds` there and the images of `ops` read from the bits of `H` below
`a`. -/
def blockOK (seeds H a L : Nat) (ops : List Nat) : Bool :=
  (H >>> a) % 2 ^ L &&& blockAcc (H % 2 ^ a) a ops ((seeds >>> a) % 2 ^ L) ==
    (H >>> a) % 2 ^ L

/-- **Soundness grows by a block.** -/
theorem Sound.mod_add {seeds H a L : Nat} {ops : List Nat} (hs : Sound seeds)
    (hP : Sound (H % 2 ^ a)) (h : blockOK seeds H a L ops = true) :
    Sound (H % 2 ^ (a + L)) := by
  intro n hn
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hn
  by_cases hna : n < a
  · exact hP n (by rw [Nat.testBit_mod_two_pow]; simp [hna, hn.2])
  have hacc := wsound_blockAcc hP a ops (hs.wsound_shiftRight a L)
  rw [blockOK, beq_iff_eq] at h
  have hb := congrArg (fun x => Nat.testBit x (n - a)) h
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    show n - a < L by omega, show a + (n - a) = n by omega, hn.2, decide_true,
    Bool.true_and] at hb
  have := hacc (n - a) hb
  rwa [show a + (n - a) = n by omega] at this

/-- **An interval above a sound bitmap is covered.** Every size in `[a, a + L)` is recorded
by the images of `ops` read from `H`. -/
def coverOK (H a L : Nat) (ops : List Nat) : Bool :=
  blockAcc H a ops 0 % 2 ^ L == 2 ^ L - 1

theorem hasModel_of_coverOK {H a L : Nat} {ops : List Nat} (hH : Sound H)
    (h : coverOK H a L ops = true) {n : Nat} (h1 : a ≤ n) (h2 : n < a + L) : Law677.HasModel n := by
  rw [coverOK, beq_iff_eq] at h
  have hb := congrArg (fun x => Nat.testBit x (n - a)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, show n - a < L by omega,
    decide_true, Bool.true_and] at hb
  have := wsound_blockAcc hH a ops (wsound_zero a) (n - a) hb
  rwa [show a + (n - a) = n by omega] at this

/-- Consecutive blocks `(L, ops)` from `a` on are all produced from below. -/
def blocksOK (seeds H : Nat) : Nat → List (Nat × List Nat) → Bool
  | _, [] => true
  | a, (L, ops) :: rest => blockOK seeds H a L ops && blocksOK seeds H (a + L) rest

/-- The end of consecutive blocks `(L, ops)` starting at `a`. -/
def blocksEnd : Nat → List (Nat × List Nat) → Nat
  | a, [] => a
  | a, (L, _) :: rest => blocksEnd (a + L) rest

/-- **Soundness grows by consecutive blocks.** -/
theorem Sound.of_blocksOK {seeds H : Nat} (hs : Sound seeds) :
    ∀ (a : Nat) (bs : List (Nat × List Nat)), Sound (H % 2 ^ a) →
      blocksOK seeds H a bs = true → Sound (H % 2 ^ blocksEnd a bs)
  | _, [], hP, _ => hP
  | a, (L, ops) :: rest, hP, h => by
    simp only [blocksOK, Bool.and_eq_true] at h
    exact Sound.of_blocksOK hs (a + L) rest (hs.mod_add hP h.1) h.2

/-- Consecutive intervals `(L, ops)` from `a` on are all covered. -/
def coversOK (H : Nat) : Nat → List (Nat × List Nat) → Bool
  | _, [] => true
  | a, (L, ops) :: rest => coverOK H a L ops && coversOK H (a + L) rest

/-- **Covered intervals above a sound bitmap**: every size from the start of the first
interval to the end of the last carries a model. -/
theorem hasModel_of_coversOK {H : Nat} (hH : Sound H) :
    ∀ (a : Nat) (ws : List (Nat × List Nat)), coversOK H a ws = true →
      ∀ n, a ≤ n → n < blocksEnd a ws → Law677.HasModel n
  | a, [], _, n, h1, h2 => by simp [blocksEnd] at h2; omega
  | a, (L, ops) :: rest, h, n, h1, h2 => by
    simp only [coversOK, Bool.and_eq_true] at h
    simp only [blocksEnd] at h2
    by_cases hn : n < a + L
    · exact hasModel_of_coverOK hH h.1 h1 hn
    · exact hasModel_of_coversOK hH (a + L) rest h.2 n (by omega) h2

/-- `ofWords ws acc` appends the 64-bit words `ws`, most significant first, below `acc`,
evaluating the accumulator after each word; `ofWords ws 0` is the number the words spell. -/
def ofWords : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun w _ ih acc => forceThen acc fun acc => ih (acc <<< 64 ||| w))

/-- The bits `lo, …, lo + len - 1` of `H` are all set. -/
def intervalOK (H lo len : Nat) : Bool := (H >>> lo) % 2 ^ len == 2 ^ len - 1

theorem testBit_of_intervalOK {H lo len : Nat} (h : intervalOK H lo len = true) {n : Nat}
    (h1 : lo ≤ n) (h2 : n < lo + len) : H.testBit n = true := by
  rw [intervalOK, beq_iff_eq] at h
  have hb := congrArg (fun x => Nat.testBit x (n - lo)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    show n - lo < len by omega, decide_true, Bool.true_and] at hb
  rwa [show lo + (n - lo) = n by omega] at hb

/-! ## From a long interval of orders to all large orders -/

/-- Every size in `[N, X]` carries a model. -/
def Upto (N X : Nat) : Prop := ∀ n, N ≤ n → n ≤ X → Law677.HasModel n

/-- **One step up.** If every size in `[N, X]` carries a model, and `q ∈ [N, X]` is coprime
to `P79` with `79 q + N ≤ X + 1`, then every size up to `80 q` carries a model: a size
`n > X` is `79 q + 0 + (n - 79 q)` with `n - 79 q ∈ [N, q]`. -/
theorem Upto.extend {N X q : Nat} (hX : Upto N X) (hg : Nat.gcd q P79 = 1) (hNq : N ≤ q)
    (hq : 79 * q + N ≤ X + 1) : Upto N (80 * q) := by
  intro n hn1 hn2
  by_cases hnX : n ≤ X
  · exact hX n hn1 hnX
  have hqX : q ≤ X := by omega
  have := hasModel_trunc (s := 0) (r := n - 79 * q) hg (Nat.zero_le q) (by omega)
    (hX q hNq hqX) Law677.hasModel_zero (hX _ (by omega) (by omega))
  rwa [show 79 * q + 0 + (n - 79 * q) = n by omega] at this

/-- The first `q` coprime to `P79` found counting down from the argument, among `fuel`
candidates, or `0` if there is none. -/
def findGood (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih q => if Nat.gcd q P79 == 1 then q else ih (q - 1)) fuel

/-- One step of the chain from `[N, X]`: the new right end `max X (80 q)` for the
`q ≤ (X + 1 - N) / 79` coprime to `P79` that `findGood` finds, when `N ≤ q` and
`79 q + N ≤ X + 1`; otherwise `X`. -/
def chainStep (N X : Nat) : Nat :=
  let q := findGood 1000 ((X + 1 - N) / 79)
  if Nat.gcd q P79 == 1 && decide (N ≤ q) && decide (79 * q + N ≤ X + 1) then max X (80 * q)
  else X

theorem Upto.chainStep {N X : Nat} (hX : Upto N X) : Upto N (chainStep N X) := by
  unfold OrderBitmap.chainStep
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have h' := hX.extend h.1.1 h.1.2 h.2
    intro n hn1 hn2
    by_cases hn : n ≤ X
    · exact hX n hn1 hn
    · exact h' n hn1 (by omega)
  · exact hX

/-- Iterate `chainStep` `steps` times, evaluating each result before the next step. -/
def chain (N : Nat) (steps : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun _ ih X => forceThen X fun X => ih (chainStep N X)) steps

/-- **The chain is sound**: every size in the interval it reaches carries a model. -/
theorem Upto.chain {N : Nat} :
    ∀ (steps : Nat) {X : Nat}, Upto N X → Upto N (OrderBitmap.chain N steps X)
  | 0, _, hX => hX
  | steps + 1, X, hX => by
    change Upto N (forceThen X fun X => OrderBitmap.chain N steps (OrderBitmap.chainStep N X))
    rw [forceThen_eq]
    exact Upto.chain steps hX.chainStep

/-- **The tail.** If every size in `[N, X]` carries a model and `X ≥ 80 (79 (P79 + 2) + N)`,
then every size `n ≥ N` does: for `n > X`, some `q ≡ 1 (mod P79)` with
`n / 80 < q ≤ n / 80 + P79 + 2` is coprime to `P79`, and `n - 79 q` lies in `[N, q]`. -/
theorem Upto.tail {N X : Nat} (hX : Upto N X) (hbig : 80 * (79 * (P79 + 2) + N) ≤ X) :
    ∀ n, N ≤ n → Law677.HasModel n := by
  intro n
  refine Nat.strongRecOn (motive := fun n => N ≤ n → Law677.HasModel n) n ?_
  intro n ih hn
  by_cases hnX : n ≤ X
  · exact hX n hn hnX
  have hP : 1 < P79 := by decide
  obtain ⟨c, hc⟩ : ∃ c, c = (n + 79) / 80 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = P79 * (c / P79) := ⟨_, rfl⟩
  have hm1 : m ≤ c := hm ▸ Nat.mul_div_le c P79
  have hm2 : c < m + P79 := by
    have := Nat.lt_mul_div_succ c (by omega : 0 < P79)
    rw [Nat.mul_add, Nat.mul_one, ← hm] at this
    exact this
  obtain ⟨q, hq⟩ : ∃ q, q = m + P79 + 1 := ⟨_, rfl⟩
  have hg : Nat.gcd q P79 = 1 := by
    have hqmod : q % P79 = 1 := by
      rw [hq, hm, show P79 * (c / P79) + P79 + 1 = P79 * (c / P79 + 1) + 1 by
        rw [Nat.mul_add, Nat.mul_one], Nat.mul_add_mod, Nat.mod_eq_of_lt hP]
    rw [Nat.gcd_comm, Nat.gcd_rec, hqmod, Nat.gcd_one_left]
  have hc1 : 80 * c ≤ n + 79 := hc ▸ Nat.mul_div_le (n + 79) 80
  have hc2 : n + 79 < 80 * c + 80 := by
    have := Nat.lt_mul_div_succ (n + 79) (by omega : 0 < 80)
    rw [← hc] at this
    omega
  have h80 : n ≤ 80 * q := by omega
  have h79q : 79 * q + N ≤ n := by omega
  have hqn : q < n := by omega
  have hNq : N ≤ q := by omega
  have := hasModel_trunc (s := 0) (r := n - 79 * q) hg (Nat.zero_le q) (by omega)
    (ih q hqn hNq) Law677.hasModel_zero (ih _ (by omega) (by omega))
  rwa [show 79 * q + 0 + (n - 79 * q) = n by omega] at this

end OrderBitmap

end

end Spectrum.E677.EffectiveTail
