import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The bottom idempotent, and equation `40` over finite magmas

Equation `40`, `x ◇ x = y ◇ y`, is the heaviest target on the `definable`/finite board: a third of
its weight hangs off it, almost all of that under the two sources `4364` and `4541`. Over *all*
magmas both cells are refuted in `Definability/Semilattice.lean`, by a free semilattice whose
translation automorphism has no fixed point. Over finite magmas the same two cells go the other
way, and this file proves it.

The target asks for an operation `□` with `x □ x = y □ y`. A constant operation `x □ y := c` is the
obvious candidate, and it is definable exactly when `c` is: the graph of the constant operation is
`{(u, v, w) : w = c}`, so a formula picking `c` out is a formula defining the graph. What has to be
produced, then, is a single element of the magma nameable with no parameters. That is where
finiteness enters twice.

*An idempotent exists.* Write `v 0 = x` and `v (n+1) = x ◇ v n`. Both laws give the same recursion
for the squares along this sequence, `v (m+1) ◇ v (m+1) = x ◇ (x ◇ (v m ◇ v m))`, whence
`v m ◇ v m = v (2m+1)` by induction. On a finite carrier `v` is eventually periodic, say with
period `p` from index `i` on; taking `m = p(i+1) - 1` makes `2m + 1 = m + p(i+1)` an index congruent
to `m`, so `v m ◇ v m = v m`.

*The idempotents are a semilattice.* For both laws, `E = {a : a ◇ a = a}` is closed under `◇` and
`◇` is commutative, associative and idempotent on it -- six equational facts, each a consequence of
the law together with the idempotency of the elements involved. A finite nonempty semilattice has a
bottom element `c`, and `c` is the unique solution of
`w ◇ w = w ∧ ∀ y, (y ◇ y = y → w ◇ y = w)`,
which is a first-order formula in the magma language with no parameters.

None of this survives dropping finiteness: the free semilattice has no bottom, and indeed no
`0`-definable element at all.

## Main results

* `Definability40.definableOnMagma_40_of_bot`: a `0`-definable element gives `Law40`.
* `Definability40.exists_absorbing`: a finite nonempty commutative idempotent semigroup has an
  absorbing element.
* `Definability40.exists_idempotent_of_step`: the `v`-sequence argument.
* `Equation40_definableFromFin_Equation4364`, `Equation40_definableFromFin_Equation4541`.
-/

open FirstOrder FirstOrder.Language
open Law Law.MagmaLaw

namespace Definability40

/-! ### A `0`-definable element defines equation `40` -/

/-- The formula `w ◇ w = w ∧ ∀ y, (y ◇ y = y → w ◇ y = w)`, saying that `w` is the bottom of the
idempotents. Its free variable is the output slot `none` of a magma graph, so that it also serves
as a definition of the graph of the constant operation at `w`. -/
def botFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  let w0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) := Term.var (Sum.inl none)
  let w1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) := Term.var (Sum.inl none)
  let y : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) := Term.var (Sum.inr 0)
  (Term.bdEqual (Functions.apply₂ (Sum.inl ()) w0 w0) w0) ⊓
    BoundedFormula.all ((Term.bdEqual (Functions.apply₂ (Sum.inl ()) y y) y).imp
      (Term.bdEqual (Functions.apply₂ (Sum.inl ()) w1 y) w1))

/-- If `c` is the unique bottom idempotent then the constant operation at `c` has a definable
graph, and a constant operation satisfies equation `40`. -/
theorem definableOnMagma_40_of_bot {G : Type} (M : Magma G) (c : G)
    (hc : M.op c c = c) (hab : ∀ y : G, M.op y y = y → M.op c y = c)
    (huniq : ∀ d : G, M.op d d = d → (∀ y : G, M.op y y = y → M.op d y = d) → d = c) :
    Law40.DefinableOnMagma M := by
  refine ⟨⟨fun _ _ ↦ c⟩, (@Law40.models_iff G ⟨fun _ _ ↦ c⟩).mpr (fun _ _ ↦ rfl), ?_⟩
  refine ⟨botFormula G, ?_⟩
  ext v
  simp [Magma.Graph, Function.tupleGraph, Magma.FinArityOp, botFormula, Formula.Realize,
    Magma.FOStructure_funMap', Fin.snoc]
  constructor
  · rintro rfl
    exact ⟨hc, hab⟩
  · rintro ⟨h1, h2⟩
    exact (huniq _ h1 h2).symm

/-- On an empty carrier equation `40` holds vacuously, and every set of tuples is empty. -/
theorem definableOnMagma_40_of_isEmpty {G : Type} [IsEmpty G] (M : Magma G) :
    Law40.DefinableOnMagma M :=
  ⟨M, (@Law40.models_iff G M).mpr (fun x _ ↦ isEmptyElim x),
    ⟨Term.bdEqual (Term.var (Sum.inl none)) (Term.var (Sum.inl none)),
      by ext v; exact isEmptyElim (v none)⟩⟩

/-! ### The bottom of a finite semilattice -/

/-- A commutative, associative and idempotent operation on a finite nonempty type has an absorbing
element. The induction runs over an arbitrary finite subset and does not ask the absorbing element
to lie in it, which is what lets the subset shrink freely: idempotency holds everywhere, so the
element built at each step is legitimate wherever it lands. -/
theorem exists_absorbing {α : Type*} [Finite α] [Nonempty α] (f : α → α → α)
    (hc : ∀ a b, f a b = f b a) (ha : ∀ a b c, f (f a b) c = f a (f b c))
    (hi : ∀ a, f a a = a) : ∃ c, ∀ y, f c y = c := by
  classical
  have _ : Fintype α := Fintype.ofFinite α
  suffices h : ∀ s : Finset α, s.Nonempty → ∃ c, ∀ y ∈ s, f c y = c by
    obtain ⟨c, hcs⟩ := h Finset.univ Finset.univ_nonempty
    exact ⟨c, fun y ↦ hcs y (Finset.mem_univ y)⟩
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, fun y hy ↦ by rw [Finset.mem_singleton.mp hy]; exact hi a⟩
  | cons a s _ _ ih =>
    obtain ⟨c, hcs⟩ := ih
    refine ⟨f a c, fun y hy ↦ ?_⟩
    rcases Finset.mem_cons.mp hy with rfl | hy
    · rw [ha, hc c y, ← ha, hi]
    · rw [ha, hcs y hy]

/-! ### An idempotent element -/

variable {G : Type}

/-- `vseq M x n` is `x ◇ (x ◇ ⋯ ◇ x)` with `n` operations, bracketed to the right. -/
def vseq (M : Magma G) (x : G) : ℕ → G
  | 0 => x
  | n + 1 => M.op x (vseq M x n)

/-- A finite magma in which squares along the sequence `x, x ◇ x, x ◇ (x ◇ x), …` obey the
recursion `hstep` has an idempotent element.

`hstep` says that squaring commutes with one step of the sequence up to two extra steps, so the
square of the `m`-th term is the `(2m+1)`-st term. The sequence is eventually periodic, with period
`p` from index `i` on, and at `m = p(i+1) - 1` the index `2m + 1 = m + p(i+1)` is a whole number of
periods past `m`. -/
theorem exists_idempotent_of_step [Finite G] (M : Magma G) (x : G)
    (hstep : ∀ u : G, M.op (M.op x u) (M.op x u) = M.op x (M.op x (M.op u u))) :
    ∃ e : G, M.op e e = e := by
  have key : ∀ m, M.op (vseq M x m) (vseq M x m) = vseq M x (2 * m + 1) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have e1 : vseq M x (m + 1) = M.op x (vseq M x m) := rfl
      have e2 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by omega
      rw [e1, hstep, ih, e2]
      rfl
  obtain ⟨i, j, hij, hv⟩ : ∃ i j : ℕ, i < j ∧ vseq M x i = vseq M x j := by
    obtain ⟨a, b, hne, hab⟩ := Finite.exists_ne_map_eq_of_infinite (vseq M x)
    rcases hne.lt_or_gt with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  set p := j - i with hp
  have hp0 : 0 < p := by omega
  have hone : ∀ n, i ≤ n → vseq M x (n + p) = vseq M x n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have e : i + p = j := by omega
      rw [e]; exact hv.symm
    | succ n hn ih =>
      have e : n + 1 + p = n + p + 1 := by omega
      rw [e]
      show M.op x (vseq M x (n + p)) = M.op x (vseq M x n)
      rw [ih]
  have hmany : ∀ k n, i ≤ n → vseq M x (n + k * p) = vseq M x n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      have e : n + (k + 1) * p = n + k * p + p := by rw [Nat.succ_mul, ← Nat.add_assoc]
      rw [e, hone _ (hn.trans (Nat.le_add_right n (k * p))), ih n hn]
  obtain ⟨m, hm1, him⟩ : ∃ m, m + 1 = p * (i + 1) ∧ i ≤ m := by
    have h1 : 0 < p * (i + 1) := Nat.mul_pos hp0 (Nat.succ_pos i)
    have h2 : i + 1 ≤ p * (i + 1) := Nat.le_mul_of_pos_left _ hp0
    exact ⟨p * (i + 1) - 1, Nat.sub_add_cancel h1, Nat.le_pred_of_lt h2⟩
  refine ⟨vseq M x m, ?_⟩
  have e : 2 * m + 1 = m + (i + 1) * p := by rw [Nat.mul_comm (i + 1) p, ← hm1]; omega
  rw [key m, e, hmany (i + 1) m him]

/-! ### The two halves put together -/

/-- The whole argument, as a statement about one finite magma: given the squaring recursion and the
three semilattice facts about the idempotents, equation `40` is definable. -/
theorem definableOnMagma_40_of_idem [Finite G] (M : Magma G)
    (hstep : ∀ x u : G, M.op (M.op x u) (M.op x u) = M.op x (M.op x (M.op u u)))
    (hclos : ∀ a b : G, M.op a a = a → M.op b b = b → M.op (M.op a b) (M.op a b) = M.op a b)
    (hcomm : ∀ a b : G, M.op a a = a → M.op b b = b → M.op a b = M.op b a)
    (hassoc : ∀ a b c : G, M.op a a = a → M.op b b = b → M.op c c = c →
      M.op (M.op a b) c = M.op a (M.op b c)) :
    Law40.DefinableOnMagma M := by
  rcases isEmpty_or_nonempty G with _ | hne
  · exact definableOnMagma_40_of_isEmpty M
  obtain ⟨x⟩ := hne
  obtain ⟨e, he⟩ := exists_idempotent_of_step M x (hstep x)
  have _ : Nonempty {a : G // M.op a a = a} := ⟨⟨e, he⟩⟩
  obtain ⟨c, hcabs⟩ := exists_absorbing (α := {a : G // M.op a a = a})
    (fun a b ↦ ⟨M.op a.1 b.1, hclos a.1 b.1 a.2 b.2⟩)
    (fun a b ↦ Subtype.ext (hcomm a.1 b.1 a.2 b.2))
    (fun a b d ↦ Subtype.ext (hassoc a.1 b.1 d.1 a.2 b.2 d.2))
    (fun a ↦ Subtype.ext a.2)
  refine definableOnMagma_40_of_bot M c.1 c.2 (fun y hy ↦ congrArg Subtype.val (hcabs ⟨y, hy⟩))
    (fun d hd h2 ↦ ?_)
  calc d = M.op d c.1 := (h2 c.1 c.2).symm
    _ = M.op c.1 d := hcomm d c.1 hd c.2
    _ = c.1 := congrArg Subtype.val (hcabs ⟨d, hd⟩)

end Definability40

open Definability40

/-- Over finite magmas, equation `40` is definable from equation `4364`,
`x ◇ (y ◇ z) = y ◇ (z ◇ x)`: the bottom of its idempotents is a `0`-definable element, and the
constant operation there satisfies `40`. Contrast
`Equation40_not_definableFrom_Equation4364`, which refutes the same cell over all magmas. -/
theorem Equation40_definableFromFin_Equation4364 : Law40.DefinableFromFin Law4364 := by
  intro G _ M hM
  have h : ∀ x y z : G, M.op x (M.op y z) = M.op y (M.op z x) := (@Law4364.models_iff G M).mp hM
  exact definableOnMagma_40_of_idem M (by grind) (by grind) (by grind) (by grind)

/-- Over finite magmas, equation `40` is definable from equation `4541`,
`x ◇ (y ◇ z) = (z ◇ x) ◇ y`. Contrast `Equation40_not_definableFrom_Equation4541`. -/
theorem Equation40_definableFromFin_Equation4541 : Law40.DefinableFromFin Law4541 := by
  intro G _ M hM
  have h : ∀ x y z : G, M.op x (M.op y z) = M.op (M.op z x) y := (@Law4541.models_iff G M).mp hM
  exact definableOnMagma_40_of_idem M (by grind) (by grind) (by grind) (by grind)
