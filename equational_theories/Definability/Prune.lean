import DefSearch
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

/-! ### Dropping the instances that are already settled -/

/-- The instances still worth looking at, or `none` when one of them is decided the wrong way.

An instance both of whose sides the partial table determines keeps those two values under every
extension -- cells are only ever filled going down -- so if they agree the instance is settled and
never has to be looked at again below this node. `searchT` rescans all of them at every node
instead, and for a four-variable law on a carrier of nine that is thirteen hundred term evaluations
per node against a handful. -/
def sift (op : Fin n → Fin n → Option (Fin n)) (L : Law.MagmaLaw α) :
    List (α → Fin n) → Option (List (α → Fin n))
  | [] => some []
  | φ :: rest =>
      match evalP op φ L.lhs, evalP op φ L.rhs with
      | some a, some b => if a = b then sift op L rest else none
      | _, _ => (sift op L rest).map (φ :: ·)

theorem sift_eq_none {op : Fin n → Fin n → Option (Fin n)} {L : Law.MagmaLaw α} :
    ∀ envs : List (α → Fin n), sift op L envs = none → ∃ φ, violatedAt op L φ = true := by
  intro envs
  induction envs with
  | nil => intro h; exact absurd h (by simp [sift])
  | cons φ rest ih =>
    intro h
    unfold sift at h
    rcases ha : evalP op φ L.lhs with _ | a
    · rw [ha] at h; exact ih (by simpa using h)
    rcases hb : evalP op φ L.rhs with _ | b
    · rw [ha, hb] at h; exact ih (by simpa using h)
    rw [ha, hb] at h
    simp only at h
    split at h
    · exact ih h
    · exact ⟨φ, by simp [violatedAt, ha, hb, bne_iff_ne, ne_eq]; assumption⟩

/-- The backtracking search of `searchT`, carrying the instances still undecided. The verdict is
the same and so is the tree; only the work at each node is smaller. -/
def searchA (E : Fin k → Fin n → Fin n) (L : Law.MagmaLaw α) :
    List ((Fin m × List (Fin n)) × List ((Fin n × Fin n) × Fin k)) →
      Array (Option (Fin n)) → List (α → Fin n) → Bool
  | [], t, envs => (sift (tget t) L envs).isNone
  | (p, cs) :: rest, t, envs =>
      match sift (tget t) L envs with
      | none => true
      | some envs' => p.2.all fun x ↦ searchA E L rest (fill E cs x t) envs'

/-- **The search is sound.** Nothing is asked of `envs`: a violated instance refutes the law
whatever list it was found in, so dropping instances can only make the search fail. -/
theorem searchA_sound {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {L : Law.MagmaLaw α} :
    ∀ (todo : List ((Fin m × List (Fin n)) × List ((Fin n × Fin n) × Fin k)))
      (t : Array (Option (Fin n))) (envs : List (α → Fin n)),
      searchA E L todo t envs = true →
      ∀ w : Fin m → Fin n,
        (∀ x y c, tget t x y = some c → transport E tr w x y = c) →
        (∀ q ∈ todo, w q.1.1 ∈ q.1.2) →
        (∀ q ∈ todo, ∀ p ∈ q.2, tr p.1.1 p.1.2 = (q.1.1, p.2)) →
        ¬ @satisfies α (Fin n) (Magma.mk (transport E tr w)) L := by
  intro todo
  induction todo with
  | nil =>
    intro t envs hs w hc _ _
    obtain ⟨φ, hφ⟩ := sift_eq_none envs (Option.isNone_iff_eq_none.mp (by simpa [searchA] using hs))
    exact not_satisfies_of_violated hc hφ
  | cons q rest ih =>
    obtain ⟨⟨i, d⟩, cs⟩ := q
    intro t envs hs w hc h₁ h₂
    rcases hsi : sift (tget t) L envs with _ | envs'
    · obtain ⟨φ, hφ⟩ := sift_eq_none envs hsi
      exact not_satisfies_of_violated hc hφ
    · rw [searchA, hsi] at hs
      exact ih (fill E cs (w i) t) envs'
        (List.all_eq_true.mp hs (w i) (h₁ _ List.mem_cons_self)) w
        (fill_compat cs (h₂ _ List.mem_cons_self) t hc)
        (fun q hq ↦ h₁ q (List.mem_cons_of_mem _ hq))
        (fun q hq ↦ h₂ q (List.mem_cons_of_mem _ hq))

/-! ### The bridge to the native search

`searchA` is the search this file proves sound, and it is also the reason a refutation costs
minutes: `native_decide` evaluates it in the interpreter, because no module of this project is
precompiled. `DefSearch` is the same search written over `Nat` and `Array Nat` in a library that
Lake *does* precompile, which on a two-million-node tree is fifty-two times faster. What follows
is the translation, paid once before the search starts: the law's terms become `DefSearch.Tm`, the
orbits become lists of writes, and `Option (Fin n)` becomes "a value below `n`". -/

/-- A law's term as the tree the kernel takes. -/
def toTm : FreeMagma ℕ → DefSearch.Tm
  | .Leaf a => .var a
  | .Fork l r => .app (toTm l) (toTm r)

/-- The assignment an env array stands for. Reading modulo `n` means no array has to be shown to
hold values of the carrier. -/
def envφ (n : ℕ) [NeZero n] (e : Array Nat) : ℕ → Fin n :=
  fun a ↦ ⟨e.getD a 0 % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- A `Nat` table is compatible with `q` when every cell it determines holds `q`'s value there.
This is `tget`'s hypothesis with `n` in place of `none`. -/
def CompatN (n : ℕ) (q : Fin n → Fin n → Fin n) (tab : Array Nat) : Prop :=
  ∀ x y : Fin n, tab.getD (x.1 * n + y.1) n < n → tab.getD (x.1 * n + y.1) n = (q x y).1

/-- **The pruning is sound**, in the kernel's representation: a term the partial table determines
has that value under every completion. -/
theorem ev_sound {n : ℕ} [NeZero n] {q : Fin n → Fin n → Fin n} {tab : Array Nat}
    (h : CompatN n q tab) (e : Array Nat) :
    ∀ t : FreeMagma ℕ, DefSearch.ev n tab e (toTm t) < n →
      DefSearch.ev n tab e (toTm t) = (@evalInMagma ℕ (Fin n) (Magma.mk q) (envφ n e) t).1 := by
  intro t
  induction t with
  | Leaf a => intro _; rfl
  | Fork l r ihl ihr =>
    intro hlt
    have hev : DefSearch.ev n tab e (toTm (FreeMagma.Fork l r))
        = (if DefSearch.ev n tab e (toTm l) < n then
             (if DefSearch.ev n tab e (toTm r) < n then
                tab.getD (DefSearch.ev n tab e (toTm l) * n + DefSearch.ev n tab e (toTm r)) n
              else n)
           else n) := rfl
    rw [hev] at hlt ⊢
    by_cases hx : DefSearch.ev n tab e (toTm l) < n
    · rw [if_pos hx] at hlt ⊢
      by_cases hy : DefSearch.ev n tab e (toTm r) < n
      · rw [if_pos hy] at hlt ⊢
        rw [ihl hx, ihr hy] at hlt ⊢
        exact h _ _ hlt
      · rw [if_neg hy] at hlt; omega
    · rw [if_neg hx] at hlt; omega

theorem not_satisfies_of_ev {n : ℕ} [NeZero n] {q : Fin n → Fin n → Fin n} {tab : Array Nat}
    {L : Law.MagmaLaw ℕ} {e : Array Nat} (h : CompatN n q tab)
    (ha : DefSearch.ev n tab e (toTm L.lhs) < n)
    (hb : DefSearch.ev n tab e (toTm L.rhs) < n)
    (hne : DefSearch.ev n tab e (toTm L.lhs) ≠ DefSearch.ev n tab e (toTm L.rhs)) :
    ¬ @satisfies ℕ (Fin n) (Magma.mk q) L := by
  intro hs
  exact hne (by rw [ev_sound h e L.lhs ha, ev_sound h e L.rhs hb, hs (envφ n e)])

theorem sift_eq_none' {n : ℕ} {lhs rhs : DefSearch.Tm} {tab : Array Nat} :
    ∀ act : List (Array Nat), DefSearch.sift n lhs rhs tab act = none →
      ∃ e : Array Nat, DefSearch.ev n tab e lhs < n ∧ DefSearch.ev n tab e rhs < n ∧
        DefSearch.ev n tab e lhs ≠ DefSearch.ev n tab e rhs := by
  intro act
  induction act with
  | nil => intro h; exact absurd h (by simp [DefSearch.sift])
  | cons e rest ih =>
    intro h
    rw [DefSearch.sift] at h
    by_cases ha : DefSearch.ev n tab e lhs < n
    · rw [if_pos ha] at h
      by_cases hb : DefSearch.ev n tab e rhs < n
      · rw [if_pos hb] at h
        by_cases hab : (DefSearch.ev n tab e lhs == DefSearch.ev n tab e rhs) = true
        · rw [if_pos hab] at h; exact ih h
        · exact ⟨e, ha, hb, by simpa using hab⟩
      · rw [if_neg hb] at h; exact ih (by simpa using h)
    · rw [if_neg ha] at h; exact ih (by simpa using h)

theorem setIfInBounds_compatN {n : ℕ} {q : Fin n → Fin n → Fin n} {tab : Array Nat}
    {x y : Fin n} (h : CompatN n q tab) :
    CompatN n q (tab.setIfInBounds (x.1 * n + y.1) (q x y).1) := by
  intro x' y' hlt
  by_cases hidx : x.1 * n + y.1 = x'.1 * n + y'.1
  · obtain ⟨hx, hy⟩ := row_col_inj hidx
    subst hx; subst hy
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hlt ⊢
    by_cases hsz : x.1 * n + y.1 < tab.size <;> simp_all
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hidx] at hlt ⊢
    rw [← Array.getD_eq_getD_getElem?] at hlt ⊢
    exact h x' y' hlt

theorem fill_compatN {n : ℕ} {q : Fin n → Fin n → Fin n} :
    ∀ ws : List (Nat × Nat),
      (∀ p ∈ ws, ∃ x y : Fin n, p.1 = x.1 * n + y.1 ∧ p.2 = (q x y).1) →
      ∀ tab : Array Nat, CompatN n q tab → CompatN n q (DefSearch.fill ws tab) := by
  intro ws
  induction ws with
  | nil => intro _ tab h; exact h
  | cons p rest ih =>
    intro hw tab h
    obtain ⟨x, y, hp1, hp2⟩ := hw p List.mem_cons_self
    simp only [DefSearch.fill]
    refine ih (fun r hr ↦ hw r (List.mem_cons_of_mem _ hr)) _ ?_
    rw [hp1, hp2]
    exact setIfInBounds_compatN h

/-- The writes the choice `x` for orbit `i` makes: every cell that orbit owns gets the value the
mover carries there. -/
def writesOf (E : Fin k → Fin n → Fin n) (tr : Fin n → Fin n → Fin m × Fin k)
    (i : Fin m) (x : Fin n) : List (Nat × Nat) :=
  (cells tr i).map fun p ↦ (p.1.1.1 * n + p.1.2.1, (E p.2 x).1)

/-- One level of the search: the choices orbit `i` offers, digested into writes. -/
def levelOf (E : Fin k → Fin n → Fin n) (z : Fin m → Fin k) (st : Fin m → Fin k → Fin k)
    (tr : Fin n → Fin n → Fin m × Fin k) (i : Fin m) : List (List (Nat × Nat)) :=
  ((List.finRange n).filter (orbitOK E z st i ·)).map (writesOf E tr i)

/-- The whole search tree's shape, in the order `ord` names. -/
def levels (E : Fin k → Fin n → Fin n) (z : Fin m → Fin k) (st : Fin m → Fin k → Fin k)
    (tr : Fin n → Fin n → Fin m × Fin k) (ord : List (Fin m)) : List (List (List (Nat × Nat))) :=
  ord.map (levelOf E z st tr)

theorem writesOf_spec {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {w : Fin m → Fin n} (i : Fin m) :
    ∀ p ∈ writesOf E tr i (w i),
      ∃ x y : Fin n, p.1 = x.1 * n + y.1 ∧ p.2 = (transport E tr w x y).1 := by
  intro p hp
  simp only [writesOf, List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  refine ⟨c.1.1, c.1.2, rfl, ?_⟩
  show (E c.2 (w i)).1 = (transport E tr w c.1.1 c.1.2).1
  simp only [transport, tr_of_mem_cells hc]

/-- **The native search is sound.** Same statement as `searchA_sound`, same induction; only the
representation of the table, the terms and the choices has changed. -/
theorem go_sound {n m k : ℕ} [NeZero n] {E : Fin k → Fin n → Fin n}
    {tr : Fin n → Fin n → Fin m × Fin k} {z : Fin m → Fin k} {st : Fin m → Fin k → Fin k}
    {L : Law.MagmaLaw ℕ} :
    ∀ (ord : List (Fin m)) (tab : Array Nat) (act : List (Array Nat)),
      DefSearch.go n (toTm L.lhs) (toTm L.rhs) (levels E z st tr ord) tab act = true →
      ∀ w : Fin m → Fin n,
        CompatN n (transport E tr w) tab →
        (∀ i ∈ ord, orbitOK E z st i (w i)) →
        ¬ @satisfies ℕ (Fin n) (Magma.mk (transport E tr w)) L := by
  intro ord
  induction ord with
  | nil =>
    intro tab act hs w hc _
    have hsi : DefSearch.sift n (toTm L.lhs) (toTm L.rhs) tab act = none := by
      simpa [levels, DefSearch.go, Option.isNone_iff_eq_none] using hs
    obtain ⟨e, ha, hb, hne⟩ := sift_eq_none' act hsi
    exact not_satisfies_of_ev hc ha hb hne
  | cons i rest ih =>
    intro tab act hs w hc h₁
    rcases hsi : DefSearch.sift n (toTm L.lhs) (toTm L.rhs) tab act with _ | act'
    · obtain ⟨e, ha, hb, hne⟩ := sift_eq_none' act hsi
      exact not_satisfies_of_ev hc ha hb hne
    · rw [levels, List.map_cons, DefSearch.go, hsi] at hs
      have hmem : writesOf E tr i (w i) ∈ levelOf E z st tr i :=
        List.mem_map.mpr ⟨w i, List.mem_filter.mpr
          ⟨List.mem_finRange _, h₁ i List.mem_cons_self⟩, rfl⟩
      exact ih _ act' (by simpa [levels] using List.all_eq_true.mp hs _ hmem) w
        (fill_compatN _ (writesOf_spec i) tab hc)
        (fun j hj ↦ h₁ j (List.mem_cons_of_mem _ hj))

/-! ### The assignments to check at -/

/-- Every map `ℕ → Fin n` supported on `0, ..., j - 1`, as the list of its value tuples. -/
def tuples (n : ℕ) : ℕ → List (List (Fin n))
  | 0 => [[]]
  | j + 1 => (tuples n j).flatMap fun t ↦ (List.finRange n).map fun x ↦ x :: t

/-- The assignments a law in `j` variables has to be checked at. -/
def envs (n : ℕ) [NeZero n] (j : ℕ) : List (ℕ → Fin n) :=
  (tuples n j).map fun t i ↦ t.getD i 0

/-- The same assignments, as the arrays the kernel reads. Nothing is asked of this list -- a
violated instance refutes the law whatever list it was found in -- so a caller may cut it down to
one assignment per orbit of the group and the search only gets cheaper. -/
def envArrs (n : ℕ) (j : ℕ) : List (Array Nat) :=
  (tuples n j).map fun t ↦ (t.map Fin.val).toArray

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

/-- **The same obstruction, with the settled instances dropped.** Identical data to
`Law.MagmaLaw.not_definableFrom_transportSearch`; only the hypothesis is discharged by `searchA`
rather than `searchT`, which walks the same tree and does a fraction of the work at each node. This
is the one to generate: the tree an order search can find is bounded by what the compiler will
replay, so making a node cheaper raises the ceiling on which frames can be landed at all. -/
theorem not_definableFrom_transportSift (M : Magma (Fin n)) (hM : satisfies (Fin n) L')
    (E Einv : Fin k → Fin n → Fin n) (rep : Fin m → Fin n × Fin n)
    (tr : Fin n → Fin n → Fin m × Fin k) (z : Fin m → Fin k) (st : Fin m → Fin k → Fin k)
    (envs : List (β → Fin n)) (ord : List (Fin m))
    (hl : ∀ i, Function.LeftInverse (Einv i) (E i))
    (hr : ∀ i, Function.RightInverse (Einv i) (E i))
    (hE : ∀ i, M.IsEndo (E i))
    (htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧ E (tr x y).2 (rep (tr x y).1).2 = y)
    (hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i))
    (hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j))
    (hs : Magma.searchA E L
      (ord.map fun i ↦
        ((i, (List.finRange n).filter (Magma.orbitOK E z st i ·)), Magma.cells tr i))
      (Array.replicate (n * n) none) envs = true) :
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
  refine Magma.searchA_sound (tr := tr) _ _ _ hs (fun i ↦ M'.op (rep i).1 (rep i).2)
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

/-- **The obstruction, certified by the native search.** The data is that of
`Law.MagmaLaw.not_definableFrom_transportSearch` with the table, the terms and the orbit choices in
the kernel's representation, and it proves the same thing. What it buys is speed: `DefSearch` is
the one library here that Lake precompiles, so `native_decide` runs machine code on it instead of
interpreting IR, and the tree a certificate may have grows by a factor of about fifty. Since a
frame is landable exactly when its search fits in what the compiler will replay, that factor is
what decides which frames can be used at all. -/
theorem not_definableFrom_transportKernel {n m k : ℕ} [NeZero n] {L L' : Law.MagmaLaw ℕ}
    (M : Magma (Fin n)) (hM : satisfies (Fin n) L')
    (E Einv : Fin k → Fin n → Fin n) (rep : Fin m → Fin n × Fin n)
    (tr : Fin n → Fin n → Fin m × Fin k) (z : Fin m → Fin k) (st : Fin m → Fin k → Fin k)
    (envs : List (Array Nat)) (ord : List (Fin m))
    (hl : ∀ i, Function.LeftInverse (Einv i) (E i))
    (hr : ∀ i, Function.RightInverse (Einv i) (E i))
    (hE : ∀ i, M.IsEndo (E i))
    (htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧ E (tr x y).2 (rep (tr x y).1).2 = y)
    (hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i))
    (hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j))
    (hs : DefSearch.go n (Magma.toTm L.lhs) (Magma.toTm L.rhs) (Magma.levels E z st tr ord)
      (Array.replicate (n * n) n) envs = true) :
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
  refine Magma.go_sound ord _ envs hs (fun i ↦ M'.op (rep i).1 (rep i).2) ?_
    (fun i _ ↦ hok i) ?_
  · intro x y hlt
    have hn : (Array.replicate (n * n) n).getD (x.1 * n + y.1) n = n := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    omega
  · show @satisfies _ (Fin n) (Magma.mk (Magma.transport E tr
      fun i ↦ M'.op (rep i).1 (rep i).2)) L
    rw [← hop]
    exact hM'

end Law.MagmaLaw
