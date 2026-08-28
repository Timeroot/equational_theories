import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `X` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(2 3)(4 5), (2 4)(3 5), (2 4 3 5)⟩`

`End(M)` is `28` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(2 3)`, `(2 3)(4 5)`, `(2 4)(3 5)`, `(2 4 3 5)`,
`(2 5 3 4)`, `(2 5)(3 4)`. -/
def pE6X0 : Fin 6 → Fin 6 := id
def pE6X1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6X2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5
def pE6X3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6X4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3
def pE6X5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
def pE6X6 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3
def pE6X7 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2

def permE6X : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6X0
  | 1 => pE6X1
  | 2 => pE6X2
  | 3 => pE6X3
  | 4 => pE6X4
  | 5 => pE6X5
  | 6 => pE6X6
  | 7 => pE6X7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `28` self-maps that must be endomorphisms: `000000`, `010000`, `101111`,
`111111`, `222222`, `232222`, `005432`, `015432`, `004532`, `014532`, `005423`, `015423`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6X : Fin 28 → Fin 46656
  | 0 => 0
  | 1 => 6
  | 2 => 9325
  | 3 => 9331
  | 4 => 18662
  | 5 => 18668
  | 6 => 20484
  | 7 => 20490
  | 8 => 20664
  | 9 => 20670
  | 10 => 26964
  | 11 => 26970
  | 12 => 27144
  | 13 => 27150
  | 14 => 27987
  | 15 => 27993
  | 16 => 37324
  | 17 => 37330
  | 18 => 38124
  | 19 => 38130
  | 20 => 38304
  | 21 => 38310
  | 22 => 44604
  | 23 => 44610
  | 24 => 44784
  | 25 => 44790
  | 26 => 46649
  | _ => 46655

def endE6X (j : Fin 28) : Fin 6 → Fin 6 := allMaps6 (eidx6X j)

/-- Indices of the other `46628`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6X : Array Nat := #[
  0, 6, 9325, 9331, 18662, 18668, 20484, 20490, 20664, 20670, 26964, 26970, 27144, 27150, 27987,
  27993, 37324, 37330, 38124, 38130, 38304, 38310, 44604, 44610, 44784, 44790, 46649, 46655]

def xarr6X : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6X.contains i)

def xidx6X (j : Fin 46628) : Fin 46656 :=
  ⟨min (xarr6X.getD j.1 0) 46655, by omega⟩

def endX6X (j : Fin 46628) : Fin 6 → Fin 6 := allMaps6 (xidx6X j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6X` is given. -/
def uidx6X : Fin 8 → Fin 28
  | 0 => 25
  | 1 => 21
  | 2 => 23
  | 3 => 19
  | 4 => 13
  | 5 => 9
  | 6 => 11
  | 7 => 7

theorem permE6X_eq_endE6X (i : Fin 8) : permE6X i = endE6X (uidx6X i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6X : Fin 11 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)
  | 6 => (2, 0)
  | 7 => (2, 1)
  | 8 => (2, 2)
  | 9 => (2, 3)
  | 10 => (2, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6X : Fin 6 → Fin 6 → Fin 11 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 2)
  | 0, 4 => (2, 4)
  | 0, 5 => (2, 6)
  | 1, 0 => (3, 0)
  | 1, 1 => (4, 0)
  | 1, 2 => (5, 0)
  | 1, 3 => (5, 2)
  | 1, 4 => (5, 4)
  | 1, 5 => (5, 6)
  | 2, 0 => (6, 0)
  | 2, 1 => (7, 0)
  | 2, 2 => (8, 0)
  | 2, 3 => (9, 0)
  | 2, 4 => (10, 0)
  | 2, 5 => (10, 1)
  | 3, 0 => (6, 2)
  | 3, 1 => (7, 2)
  | 3, 2 => (9, 2)
  | 3, 3 => (8, 2)
  | 3, 4 => (10, 2)
  | 3, 5 => (10, 3)
  | 4, 0 => (6, 4)
  | 4, 1 => (7, 4)
  | 4, 2 => (10, 4)
  | 4, 3 => (10, 5)
  | 4, 4 => (8, 4)
  | 4, 5 => (9, 4)
  | 5, 0 => (6, 6)
  | 5, 1 => (7, 6)
  | 5, 2 => (10, 6)
  | 5, 3 => (10, 7)
  | 5, 4 => (9, 6)
  | 5, 5 => (8, 6)

/-- The `8` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6X0 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6X0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6X1 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6X1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6X2 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6X2 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `8` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6X3 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6X3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6X4 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6X4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6X5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6X5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6X6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6X6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6X7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6X7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6X8 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6X8 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6X9 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6X9 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `10`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6X10 : Fin 1 → Fin 8
  | 0 => 0

/-- The `11` orbit values named by the family's arguments. -/
def dec6X (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 11 → Fin 6
  | 0 => val6X0 a
  | 1 => val6X1 b
  | 2 => val6X2 c
  | 3 => val6X3 d
  | 4 => val6X4 e
  | 5 => val6X5 f
  | 6 => val6X6 g
  | 7 => val6X7 h
  | 8 => val6X8 i
  | 9 => val6X9 j
  | 10 => k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6X_eq_transport`). -/
def tab6X (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6X0 a
  | 0, 1 => val6X1 b
  | 0, 2 => val6X2 c
  | 0, 3 => pE6X2 (val6X2 c)
  | 0, 4 => pE6X4 (val6X2 c)
  | 0, 5 => pE6X6 (val6X2 c)
  | 1, 0 => val6X3 d
  | 1, 1 => val6X4 e
  | 1, 2 => val6X5 f
  | 1, 3 => pE6X2 (val6X5 f)
  | 1, 4 => pE6X4 (val6X5 f)
  | 1, 5 => pE6X6 (val6X5 f)
  | 2, 0 => val6X6 g
  | 2, 1 => val6X7 h
  | 2, 2 => val6X8 i
  | 2, 3 => val6X9 j
  | 2, 4 => k
  | 2, 5 => pE6X1 k
  | 3, 0 => pE6X2 (val6X6 g)
  | 3, 1 => pE6X2 (val6X7 h)
  | 3, 2 => pE6X2 (val6X9 j)
  | 3, 3 => pE6X2 (val6X8 i)
  | 3, 4 => pE6X2 k
  | 3, 5 => pE6X3 k
  | 4, 0 => pE6X4 (val6X6 g)
  | 4, 1 => pE6X4 (val6X7 h)
  | 4, 2 => pE6X4 k
  | 4, 3 => pE6X5 k
  | 4, 4 => pE6X4 (val6X8 i)
  | 4, 5 => pE6X4 (val6X9 j)
  | 5, 0 => pE6X6 (val6X6 g)
  | 5, 1 => pE6X6 (val6X7 h)
  | 5, 2 => pE6X6 k
  | 5, 3 => pE6X7 k
  | 5, 4 => pE6X6 (val6X9 j)
  | 5, 5 => pE6X6 (val6X8 i)

theorem tab6X_eq_transport (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) :
    tab6X a b c d e f g h i j k = Magma.transport permE6X tr6X (dec6X a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `393216` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6X : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6X 0 0 0 1 1 1 3 3 2 2 0
  | 1 => tab6X 0 1 3 0 1 3 0 1 2 3 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6X` is addressed. -/
def encT6X (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Nat :=
  a.1 * 196608 +
    b.1 * 98304 +
    c.1 * 24576 +
    d.1 * 12288 +
    e.1 * 6144 +
    f.1 * 1536 +
    g.1 * 384 +
    h.1 * 96 +
    i.1 * 24 +
    j.1 * 6 +
    k.1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6X` can name one
rather than search the list for it. The `393214` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6X` excludes them. Read only by `native_decide`. -/
def rankIdx6X : Nat → Nat
  | 21468 => 0
  | 182946 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6X (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 2 :=
  ⟨min (rankIdx6X (encT6X a b c d e f g h i j k)) 1, by omega⟩


/-- `2` of the `28` demanded maps and `3` of the `46628` forbidden ones, enough to separate the `2`
members from the other `393214` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6X` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6X : Fin 2 → Fin 28
  | 0 => 5
  | 1 => 6
def x0idx6X : Fin 3 → Fin 46628
  | 0 => 0
  | 1 => 18644
  | 2 => 19146

def endE06X (j : Fin 2) : Fin 6 → Fin 6 := endE6X (e0idx6X j)

def endX06X (j : Fin 3) : Fin 6 → Fin 6 := endX6X (x0idx6X j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6X (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6X i)

theorem end6X_isEndo (i : Fin 2) (j : Fin 28) : (end6X i).IsEndo (endE6X j) := by
  revert i j; native_decide

theorem end6X_not_isEndo (i : Fin 2) (j : Fin 46628) : ¬ (end6X i).IsEndo (endX6X j) := by
  revert i j; native_decide

/-- `rank6X` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6X` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6X (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6X a b c d e f g h i j k) endE06X endX06X = true) :
    mem6X (rank6X a b c d e f g h i j k) = tab6X a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6X (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6X a b c d e f g h i j k) endE06X endX06X = true) :
    ∃ idx, mem6X idx = tab6X a b c d e f g h i j k :=
  ⟨_, mem_rank6X a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6X`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6X` turns that into a member index. -/
theorem exists_end6X {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6X j))
    (hX : ∀ j, ¬ M.IsEndo (endX6X j)) : ∃ i, end6X i = M := by
  have hP : ∀ i, M.IsEndo (permE6X i) := by
    intro i; rw [permE6X_eq_endE6X]; exact hE (uidx6X i)
  have hop : M.op = Magma.transport permE6X tr6X (fun i ↦ M.op (rep6X i).1 (rep6X i).2) :=
    Magma.op_eq_transport (rep := rep6X) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X0) (a := (rep6X 0).1) (b := (rep6X 0).2)
    (val := val6X0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X1) (a := (rep6X 1).1) (b := (rep6X 1).2)
    (val := val6X1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X2) (a := (rep6X 2).1) (b := (rep6X 2).2)
    (val := val6X2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X3) (a := (rep6X 3).1) (b := (rep6X 3).2)
    (val := val6X3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X4) (a := (rep6X 4).1) (b := (rep6X 4).2)
    (val := val6X4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X5) (a := (rep6X 5).1) (b := (rep6X 5).2)
    (val := val6X5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X6) (a := (rep6X 6).1) (b := (rep6X 6).2)
    (val := val6X6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X7) (a := (rep6X 7).1) (b := (rep6X 7).2)
    (val := val6X7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X8) (a := (rep6X 8).1) (b := (rep6X 8).2)
    (val := val6X8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X9) (a := (rep6X 9).1) (b := (rep6X 9).2)
    (val := val6X9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6X) (idx := stabIdx6X10) (a := (rep6X 10).1) (b := (rep6X 10).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6X a b c d e f g h i j k = fun i ↦ M.op (rep6X i).1 (rep6X i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
    · exact hi
    · exact hj
    · exact hk
  have key : tab6X a b c d e f g h i j k = M.op := by
    rw [tab6X_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6X a b c d e f g h i j k) endE06X endX06X = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6X j), fun j ↦ hX (x0idx6X j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6X a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`28` monoid of `Magma.endE6X`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6X {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6X i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6X j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6X i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6X
    (fun k ↦ (Magma.end6X_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6X_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
