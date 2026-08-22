import equational_theories.Definability.Transport

/-!
# Symmetry refutations by pruned search

`Law.MagmaLaw.not_definableFrom_transportExact` walks the whole invariant family. That is fine
while the family is a few thousand operations and hopeless past a few hundred thousand, and the
sources that are left have models whose families run to millions and billions -- a SAT solver
settles those in milliseconds, but the certificate it produces is not something `native_decide`
can replay.

The family does not have to be walked. Its members are built one orbit value at a time by
`Magma.transport`, and a partial choice already fills part of the table: every pair in an orbit
whose value has been chosen. Most instances of the target law are decided by that partial table
long before the last orbit is reached, and an instance that is decided *and violated* kills the
whole subtree. What is left is a backtracking search whose cost is the size of the pruned tree,
and in practice that is some five orders of magnitude below the family -- a family of `6 ^ 12`
falls in five thousand nodes.

The soundness of the pruning is `Magma.evalP_eq`: a term that evaluates to `some c` under the
partial table evaluates to `c` under every completion, because `Magma.evalP` returns `none` the
moment it meets an unfilled cell. So a partial assignment exhibiting two sides of the law with
different determined values cannot be extended to a model, and the search may skip it. Notice
what is *not* needed: no claim that the table is filled far enough for anything. A search that
reaches a leaf without finding a violation simply returns `false`.

The search carries the partially filled table rather than the choice of orbit values it came
from. That is not cosmetic. `native_decide` runs in the interpreter, where reading a value back
through `Magma.transport` costs a lookup in `tr`, a walk down the assignment and an application of
`E`, all of it repeated at every one of the several hundred table accesses a node makes; carrying
the table makes each of them a single array index, and filling an orbit writes the handful of
cells it owns.

## Contents

* `Magma.tget` and `Magma.fill` -- the partially filled table, and filling one orbit of it;
* `Magma.evalP` and `Magma.evalP_eq` -- partial term evaluation and its soundness;
* `Magma.violatedAt` -- an instance of the law already decided the wrong way;
* `Magma.searchT` -- the backtracking search, and `Magma.searchT_sound`;
* `Law.MagmaLaw.not_definableFrom_transportSearch` -- the obstruction it certifies.
-/

open Law Law.MagmaLaw FreeMagma

namespace Magma

variable {α : Type*} {n m k : ℕ}

/-! ### The partially filled table -/

/-- The partial operation a table stands for: the cell at `x * n + y`, `none` where the orbit of
`(x, y)` has not been given a value yet. -/
def tget (t : Array (Option (Fin n))) (x y : Fin n) : Option (Fin n) :=
  t.getD (x.1 * n + y.1) none

@[simp] theorem tget_replicate {N : ℕ} (x y : Fin n) :
    tget (n := n) (Array.replicate N none) x y = none := by
  rw [tget, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem row_col_inj {x y x' y' : Fin n} (h : x.1 * n + y.1 = x'.1 * n + y'.1) :
    x = x' ∧ y = y' := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hy : y.1 = y'.1 := by
    have := congrArg (· % n) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt y.isLt, Nat.mod_eq_of_lt y'.isLt] using this
  exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right hn (by omega)), Fin.ext hy⟩

/-- Writing one cell keeps the table compatible with `q`, provided the value written is the one
`q` has there. -/
theorem tget_set_compat {q : Fin n → Fin n → Fin n} {t : Array (Option (Fin n))} {x y c : Fin n}
    (h : ∀ x y c, tget t x y = some c → q x y = c) (hc : q x y = c) :
    ∀ x' y' c', tget (t.setIfInBounds (x.1 * n + y.1) (some c)) x' y' = some c' → q x' y' = c' := by
  intro x' y' c' hc'
  by_cases hidx : x.1 * n + y.1 = x'.1 * n + y'.1
  · obtain ⟨hx, hy⟩ := row_col_inj hidx
    subst hx; subst hy
    rw [tget, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hc'
    rw [hc]
    by_cases hsz : x.1 * n + y.1 < t.size <;> simp_all
  · rw [tget, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hidx] at hc'
    exact h _ _ _ (by rw [tget, Array.getD_eq_getD_getElem?]; exact hc')

/-- Which pairs orbit `i` owns, each with the permutation index `tr` records there. -/
def cells (tr : Fin n → Fin n → Fin m × Fin k) (i : Fin m) : List ((Fin n × Fin n) × Fin k) :=
  (List.finRange n).flatMap fun x ↦ (List.finRange n).filterMap fun y ↦
    if (tr x y).1 = i then some ((x, y), (tr x y).2) else none

theorem tr_of_mem_cells {tr : Fin n → Fin n → Fin m × Fin k} {i : Fin m}
    {p : (Fin n × Fin n) × Fin k} (h : p ∈ cells tr i) : tr p.1.1 p.1.2 = (i, p.2) := by
  simp only [cells, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at h
  obtain ⟨x, y, hy⟩ := h
  split at hy
  · obtain ⟨rfl⟩ := Option.some.inj hy
    exact Prod.ext (by assumption) rfl
  · exact absurd hy (by simp)

/-- Give orbit `i` the value `c`: every pair it owns gets that value moved into place. -/
def fill (E : Fin k → Fin n → Fin n) (cs : List ((Fin n × Fin n) × Fin k)) (c : Fin n)
    (t : Array (Option (Fin n))) : Array (Option (Fin n)) :=
  cs.foldl (fun t p ↦ t.setIfInBounds (p.1.1.1 * n + p.1.2.1) (some (E p.2 c))) t

theorem fill_compat {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {w : Fin m → Fin n} {i : Fin m} :
    ∀ (cs : List ((Fin n × Fin n) × Fin k)), (∀ p ∈ cs, tr p.1.1 p.1.2 = (i, p.2)) →
      ∀ t : Array (Option (Fin n)),
        (∀ x y c, tget t x y = some c → transport E tr w x y = c) →
        ∀ x y c, tget (fill E cs (w i) t) x y = some c → transport E tr w x y = c := by
  intro cs
  induction cs with
  | nil => intro _ t h; exact h
  | cons p rest ih =>
    intro hcs t h
    refine ih (fun q hq ↦ hcs q (List.mem_cons_of_mem _ hq)) _ ?_
    refine tget_set_compat h ?_
    show E (tr p.1.1 p.1.2).2 (w (tr p.1.1 p.1.2).1) = E p.2 (w i)
    rw [hcs p List.mem_cons_self]

/-! ### Partial evaluation -/

/-- Evaluation of a term under a partial operation: `none` as soon as any subterm is undetermined.
-/
def evalP (op : Fin n → Fin n → Option (Fin n)) (φ : α → Fin n) : FreeMagma α → Option (Fin n)
  | .Leaf a => some (φ a)
  | .Fork l r => (evalP op φ l).bind fun x ↦ (evalP op φ r).bind fun y ↦ op x y

/-- **The pruning is sound.** A determined partial value is the value of every completion. -/
theorem evalP_eq {op : Fin n → Fin n → Option (Fin n)} {q : Fin n → Fin n → Fin n}
    (h : ∀ x y c, op x y = some c → q x y = c) (φ : α → Fin n) :
    ∀ (t : FreeMagma α) (c : Fin n), evalP op φ t = some c →
      @evalInMagma α (Fin n) (Magma.mk q) φ t = c := by
  intro t
  induction t with
  | Leaf a => intro c hc; exact Option.some.inj hc
  | Fork l r ihl ihr =>
    intro c hc
    simp only [evalP, Option.bind_eq_some_iff] at hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hc
    show q (@evalInMagma α (Fin n) (Magma.mk q) φ l) (@evalInMagma α (Fin n) (Magma.mk q) φ r) = c
    rw [ihl x hx, ihr y hy]
    exact h x y c hxy

/-- An instance of the law whose two sides are both determined and differ. -/
def violatedAt (op : Fin n → Fin n → Option (Fin n)) (L : Law.MagmaLaw α) (φ : α → Fin n) : Bool :=
  match evalP op φ L.lhs, evalP op φ L.rhs with
  | some a, some b => a != b
  | _, _ => false

theorem not_satisfies_of_violated {op : Fin n → Fin n → Option (Fin n)}
    {q : Fin n → Fin n → Fin n} {L : Law.MagmaLaw α} {φ : α → Fin n}
    (h : ∀ x y c, op x y = some c → q x y = c) (hv : violatedAt op L φ = true) :
    ¬ @satisfies α (Fin n) (Magma.mk q) L := by
  intro hs
  have hφ : @evalInMagma α (Fin n) (Magma.mk q) φ L.lhs
      = @evalInMagma α (Fin n) (Magma.mk q) φ L.rhs := hs φ
  unfold violatedAt at hv
  rcases ha : evalP op φ L.lhs with _ | a
  · rw [ha] at hv; simp at hv
  rcases hb : evalP op φ L.rhs with _ | b
  · rw [ha, hb] at hv; simp at hv
  rw [ha, hb] at hv
  simp only [bne_iff_ne, ne_eq] at hv
  exact hv ((evalP_eq h φ L.lhs a ha).symm.trans (hφ.trans (evalP_eq h φ L.rhs b hb)))

/-! ### The search -/

/-- The backtracking search. Each entry of `todo` is an orbit still to be assigned, the values it
may take, and the cells it owns; `t` is the table filled so far. At every node the determined
instances of the law are checked, and a violated one prunes the subtree. -/
def searchT (E : Fin k → Fin n → Fin n) (L : Law.MagmaLaw α) (envs : List (α → Fin n)) :
    List ((Fin m × List (Fin n)) × List ((Fin n × Fin n) × Fin k)) →
      Array (Option (Fin n)) → Bool
  | [], t => envs.any (violatedAt (tget t) L)
  | (p, cs) :: rest, t =>
      envs.any (violatedAt (tget t) L) ||
        p.2.all fun x ↦ searchT E L envs rest (fill E cs x t)

/-- **The search is sound.** If it succeeds then no way of filling the orbits still to be assigned
gives an operation satisfying the law. -/
theorem searchT_sound {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {L : Law.MagmaLaw α} {envs : List (α → Fin n)} :
    ∀ (todo : List ((Fin m × List (Fin n)) × List ((Fin n × Fin n) × Fin k)))
      (t : Array (Option (Fin n))),
      searchT E L envs todo t = true →
      ∀ w : Fin m → Fin n,
        (∀ x y c, tget t x y = some c → transport E tr w x y = c) →
        (∀ q ∈ todo, w q.1.1 ∈ q.1.2) →
        (∀ q ∈ todo, ∀ p ∈ q.2, tr p.1.1 p.1.2 = (q.1.1, p.2)) →
        ¬ @satisfies α (Fin n) (Magma.mk (transport E tr w)) L := by
  intro todo
  induction todo with
  | nil =>
    intro t hs w hc _ _
    obtain ⟨φ, _, hφ⟩ := List.any_eq_true.mp hs
    exact not_satisfies_of_violated hc hφ
  | cons q rest ih =>
    obtain ⟨⟨i, d⟩, cs⟩ := q
    intro t hs w hc h₁ h₂
    rcases Bool.or_eq_true_iff.mp hs with hany | hall
    · obtain ⟨φ, _, hφ⟩ := List.any_eq_true.mp hany
      exact not_satisfies_of_violated hc hφ
    · exact ih (fill E cs (w i) t) (List.all_eq_true.mp hall (w i) (h₁ _ List.mem_cons_self)) w
        (fill_compat cs (h₂ _ List.mem_cons_self) t hc)
        (fun q hq ↦ h₁ q (List.mem_cons_of_mem _ hq))
        (fun q hq ↦ h₂ q (List.mem_cons_of_mem _ hq))

/-! ### The assignments to check at -/

/-- Every map `ℕ → Fin n` supported on `0, ..., j - 1`, as the list of its value tuples. -/
def tuples (n : ℕ) : ℕ → List (List (Fin n))
  | 0 => [[]]
  | j + 1 => (tuples n j).flatMap fun t ↦ (List.finRange n).map fun x ↦ x :: t

/-- The assignments a law in `j` variables has to be checked at. -/
def envs (n : ℕ) [NeZero n] (j : ℕ) : List (ℕ → Fin n) :=
  (tuples n j).map fun t i ↦ t.getD i 0

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β} {n m k : ℕ}

/-- **The symmetry obstruction, certified by a pruned search.** The data is exactly that of
`Law.MagmaLaw.not_definableFrom_transportExact`, plus `ord`; only the final hypothesis changes,
from a walk of the invariant family to a backtracking search over it. The two prove the same thing,
and the search is what makes carriers whose families run to millions affordable.

`ord` is the sequence the orbits are assigned in, and nothing is asked of it: an `ord` that omits
an orbit leaves that orbit's cells unfilled, which can only make the search fail, and one that
repeats an orbit only wastes a level. What it is not is inconsequential -- a violated instance
prunes a subtree, so an order that determines instances of the law early prunes near the root, and
picking a good one has been worth a factor of thirty. -/
theorem not_definableFrom_transportSearch (M : Magma (Fin n)) (hM : satisfies (Fin n) L')
    (E Einv : Fin k → Fin n → Fin n) (rep : Fin m → Fin n × Fin n)
    (tr : Fin n → Fin n → Fin m × Fin k) (z : Fin m → Fin k) (st : Fin m → Fin k → Fin k)
    (envs : List (β → Fin n)) (ord : List (Fin m))
    (hl : ∀ i, Function.LeftInverse (Einv i) (E i))
    (hr : ∀ i, Function.RightInverse (Einv i) (E i))
    (hE : ∀ i, M.IsEndo (E i))
    (htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧ E (tr x y).2 (rep (tr x y).1).2 = y)
    (hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i))
    (hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j))
    (hs : Magma.searchT E L envs
      (ord.map fun i ↦
        ((i, (List.finRange n).filter (Magma.orbitOK E z st i ·)), Magma.cells tr i))
      (Array.replicate (n * n) none) = true) :
    ¬ L.DefinableFrom L' := by
  intro h
  obtain ⟨M', hM', hd⟩ := h M hM
  have hE' : ∀ i, M'.IsEndo (E i) := fun i ↦
    Magma.IsEndo.of_definable (e := ⟨E i, Einv i, hl i, hr i⟩) hd (hE i)
  have hop : M'.op = Magma.transport E tr (fun i ↦ M'.op (rep i).1 (rep i).2) :=
    Magma.op_eq_transport (rep := rep) hE' htr
  have hfix : ∀ i, E (z i) (M'.op (rep i).1 (rep i).2) = M'.op (rep i).1 (rep i).2 := by
    intro i
    have h1 := congrFun (congrFun hop (rep i).1) (rep i).2
    simp only [Magma.transport, hz i] at h1
    exact h1.symm
  have hok : ∀ i, Magma.orbitOK E z st i (M'.op (rep i).1 (rep i).2) := by
    intro i
    simp only [Magma.orbitOK, decide_eq_true_eq]
    intro j
    rw [hfix i]
    have h2 := hE' j (rep i).1 (rep i).2
    rw [congrFun (congrFun hop (E j (rep i).1)) (E j (rep i).2)] at h2
    simpa only [Magma.transport, hst i j] using h2
  refine Magma.searchT_sound (tr := tr) _ _ hs (fun i ↦ M'.op (rep i).1 (rep i).2)
    (fun x y c hc ↦ absurd hc (by simp)) (fun q hq ↦ ?_) (fun q hq p hp ↦ ?_) ?_
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp hq
    subst hi
    exact List.mem_filter.mpr ⟨List.mem_finRange _, hok i⟩
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp hq
    subst hi
    exact Magma.tr_of_mem_cells hp
  · show @satisfies _ (Fin n) (Magma.mk (Magma.transport E tr
      fun i ↦ M'.op (rep i).1 (rep i).2)) L
    rw [← hop]
    exact hM'

end Law.MagmaLaw
