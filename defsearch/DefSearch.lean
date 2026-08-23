/-!
# The pruned search, as native code

`Definability/Prune.lean` explains what this search is and proves it sound; this file is only its
implementation, and it exists apart from the rest of the project for one reason: it is the only
library here that Lake precompiles.

`native_decide` does not compile anything. It hands the expression to Lean's evaluator, which runs
the *interpreter* on IR unless the declarations it meets live in a module that was built into a
shared library -- and nothing in `equational_theories` is. Measured on one refutation (equation 504
over the `prn9h6a` frame, two million branch nodes) the difference is 434 seconds interpreted
against 8 seconds compiled, a factor of fifty-two. Since what can be landed at all is decided by
how big a tree the certificate may have, that factor is the ceiling on the whole method.

Getting it means the inner loop must not leave this module, so nothing here may mention `Fin`,
`Array (Option _)`, `FreeMagma` or any other type from `Mathlib` or from `equational_theories`: a
call out to a declaration in a module that is not precompiled runs interpreted, and one such call
per node is enough to give the factor back. Everything is `Nat` and `Array Nat`, and the frame data
arrives pre-digested as lists of writes. The bridge to the real statement -- terms, magmas,
`DefinableFrom` -- is `Law.MagmaLaw.not_definableFrom_transportKernel`, and it is paid once, before
the search starts.

The value `n` doubles as "not determined yet": a table entry, or the result of evaluating a term,
is a value of the carrier when it is `< n` and undetermined otherwise. That is what `Option (Fin n)`
said before, without the allocation.
-/

namespace DefSearch

/-- A term over the variables `0, 1, ...`, which is `FreeMagma ℕ` with nothing attached. -/
inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  deriving Inhabited

/-- Evaluation under a partially filled `n × n` table. `n` is returned as soon as any subterm is
undetermined, so a result `< n` is a value every completion of the table agrees on. A variable is
always determined: `e` is read modulo `n`, which costs one instruction and saves the caller from
having to prove anything about its entries. -/
def ev (n : Nat) (tab : Array Nat) (e : Array Nat) : Tm → Nat
  | .var i => e.getD i 0 % n
  | .app a b =>
      let x := ev n tab e a
      if x < n then
        let y := ev n tab e b
        if y < n then tab.getD (x * n + y) n else n
      else n

/-- The instances still undecided, or `none` when one of them is decided the wrong way.

An instance both of whose sides the table determines keeps those values under every extension --
cells are only filled going down -- so if the two agree it is settled and never has to be looked at
again below this node. Rescanning all of them at every node instead costs about a third of the
search. -/
def sift (n : Nat) (lhs rhs : Tm) (tab : Array Nat) :
    List (Array Nat) → Option (List (Array Nat))
  | [] => some []
  | e :: rest =>
      let a := ev n tab e lhs
      let b := ev n tab e rhs
      if a < n then
        if b < n then
          if a == b then sift n lhs rhs tab rest else none
        else (sift n lhs rhs tab rest).map (e :: ·)
      else (sift n lhs rhs tab rest).map (e :: ·)

/-- Perform a level's writes. Out-of-range positions are ignored, which cannot happen. -/
def fill : List (Nat × Nat) → Array Nat → Array Nat
  | [], tab => tab
  | p :: rest, tab => fill rest (tab.setIfInBounds p.1 p.2)

/-! ### Choosing what to branch on

The order the orbits are assigned in changes nothing about what the search proves and everything
about how big it is. It used to be data the certificate carried, found by an offline hill-climb over
random permutations; that search cost hours per frame and the orders it found were still ten to a
hundred times worse than they could be, because one order has to serve the whole tree.

It does not have to be data at all. Nothing in the soundness proof cares *which* orbit a node
branches on -- only that every value of that orbit is tried and the rest are assigned below. So the
node may look at the table in front of it and pick: the cell that the most still-undecided instances
are waiting on. That is unit propagation, with no proof obligation attached. Measured against the
best orders the offline search ever found, it is between eighteen and eighteen thousand times fewer
nodes. -/

/-- The value of a term, together with the last cell an evaluation of it found unfilled -- `n * n`
when nothing was missing. The value is exactly `ev`'s; the cell is what the branching choice is made
from, since an instance that will not evaluate is waiting on precisely that cell. -/
def evS (n : Nat) (tab : Array Nat) (e : Array Nat) : Tm → Nat × Nat
  | .var i => (e.getD i 0 % n, n * n)
  | .app a b =>
      let x := evS n tab e a
      let y := evS n tab e b
      let s := if y.2 < n * n then y.2 else x.2
      if x.1 < n then
        if y.1 < n then
          let c := x.1 * n + y.1
          let v := tab.getD c n
          if v < n then (v, s) else (n, c)
        else (n, s)
      else (n, s)

/-- Over the instances still active, how many are waiting on each cell. -/
def votes (n : Nat) (lhs rhs : Tm) (tab : Array Nat) :
    List (Array Nat) → Array Nat → Array Nat
  | [], v => v
  | e :: rest, v =>
      let sl := (evS n tab e lhs).2
      let sr := (evS n tab e rhs).2
      let v := if sl < n * n then v.modify sl (· + 1) else v
      let v := if sr < n * n then v.modify sr (· + 1) else v
      votes n lhs rhs tab rest v

/-- How many waiting instances a level would answer. The cells an orbit owns are the positions its
first choice writes -- every choice of an orbit writes the same cells, only different values. -/
def levelScore (v : Array Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => v.getD p.1 0 + levelScore v rest

/-- The position in `todo` of the level with the most instances waiting on it. -/
def pick (v : Array Nat) : Nat → Nat → Nat → List (List (List (Nat × Nat))) → Nat
  | _, bi, _, [] => bi
  | i, bi, bs, l :: rest =>
      let s := levelScore v (l.headD [])
      if bs < s then pick v (i + 1) i s rest else pick v (i + 1) bi bs rest

/-- Take the entry at position `i` out of a list, returning it and what is left. -/
def pluck {α : Type _} : Nat → List α → Option (α × List α)
  | _, [] => none
  | 0, a :: as => some (a, as)
  | i + 1, a :: as => (pluck i as).map fun r ↦ (r.1, a :: r.2)

theorem pluck_split {α : Type _} : ∀ (l : List α) (i : Nat) (a : α) (rest : List α),
    pluck i l = some (a, rest) → ∃ p s : List α, l = p ++ a :: s ∧ rest = p ++ s := by
  intro l
  induction l with
  | nil => intro i a rest h; exact absurd h (by simp [pluck])
  | cons b bs ih =>
    intro i a rest h
    cases i with
    | zero =>
      simp only [pluck, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[], bs, by simp [h.1], by simp [h.2]⟩
    | succ j =>
      simp only [pluck, Option.map_eq_some_iff] at h
      obtain ⟨⟨a', rest'⟩, hr, hr2⟩ := h
      simp only [Prod.mk.injEq] at hr2
      obtain ⟨ha, hrest⟩ := hr2
      subst ha; subst hrest
      obtain ⟨p, s, h1, h2⟩ := ih j _ _ hr
      exact ⟨b :: p, s, by rw [h1]; rfl, by rw [h2]; rfl⟩

theorem pluck_mem {α : Type _} {a : α} {rest : List α} (i : Nat) (l : List α)
    (h : pluck i l = some (a, rest)) : a ∈ l := by
  obtain ⟨p, s, h1, -⟩ := pluck_split l i a rest h
  simp [h1]

theorem pluck_sub {α : Type _} {a : α} {rest : List α} (i : Nat) (l : List α)
    (h : pluck i l = some (a, rest)) : ∀ x ∈ rest, x ∈ l := by
  obtain ⟨p, s, h1, h2⟩ := pluck_split l i a rest h
  intro x hx
  rw [h2] at hx
  rw [h1]
  rcases List.mem_append.mp hx with h3 | h3
  · exact List.mem_append.mpr (Or.inl h3)
  · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h3))

theorem pluck_length {α : Type _} {a : α} {rest : List α} (i : Nat) (l : List α)
    (h : pluck i l = some (a, rest)) : rest.length + 1 = l.length := by
  obtain ⟨p, s, h1, h2⟩ := pluck_split l i a rest h
  rw [h1, h2]
  simp
  omega

theorem pluck_map {α β : Type _} (f : α → β) :
    ∀ (i : Nat) (l : List α),
      pluck i (l.map f) = (pluck i l).map (fun r ↦ (f r.1, r.2.map f)) := by
  intro i l
  induction l generalizing i with
  | nil => simp [pluck]
  | cons b bs ih =>
    cases i with
    | zero => simp [pluck]
    | succ j => simp [pluck, ih j, Option.map_map, Function.comp_def]

/-- The backtracking search. Each level of `todo` is the choices one orbit offers, a choice being
the cells it owns and what they get; `act` is the instances not yet settled. The answer is `true`
when no way of making the remaining choices avoids violating the law.

`fuel` only has to reach `todo.length`; the caller passes exactly that, and the structural recursion
on it is what saves the definition from a well-founded one -- the list shrinks by `pluck`, which is
not a subterm. -/
def go (n : Nat) (lhs rhs : Tm) :
    Nat → List (List (List (Nat × Nat))) → Array Nat → List (Array Nat) → Bool
  | _, [], tab, act => (sift n lhs rhs tab act).isNone
  | 0, _ :: _, _, _ => false
  | f + 1, l0 :: ls, tab, act =>
      match sift n lhs rhs tab act with
      | none => true
      | some act' =>
          match pluck (pick (votes n lhs rhs tab act' (Array.replicate (n * n) 0)) 0 0 0
              (l0 :: ls)) (l0 :: ls) with
          | none => false
          | some (opts, rest) => opts.all fun w ↦ go n lhs rhs f rest (fill w tab) act'

end DefSearch
