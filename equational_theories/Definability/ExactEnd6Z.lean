import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `Z` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 2)(1 4)(3 5), (0 2)(1 4 3 5)⟩`

`End(M)` is `36` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `9` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(1 3)`, `(1 3)(4 5)`, `(0 2)(1 4)(3 5)`, `(0 2)(1
4 3 5)`, `(0 2)(1 5 3 4)`, `(0 2)(1 5)(3 4)`. -/
def pE6Z0 : Fin 6 → Fin 6 := id
def pE6Z1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6Z2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5
def pE6Z3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4
def pE6Z4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 3
def pE6Z5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 1
def pE6Z6 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 3
def pE6Z7 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1

def permE6Z : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6Z0
  | 1 => pE6Z1
  | 2 => pE6Z2
  | 3 => pE6Z3
  | 4 => pE6Z4
  | 5 => pE6Z5
  | 6 => pE6Z6
  | 7 => pE6Z7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `36` self-maps that must be endomorphisms: `000000`, `202000`, `230131`,
`032131`, `210331`, `012331`, `250431`, `052431`, `240531`, `042531`, `020222`, `222222`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6Z : Fin 36 → Fin 46656
  | 0 => 0
  | 1 => 74
  | 2 => 11900
  | 3 => 11970
  | 4 => 12320
  | 5 => 12390
  | 6 => 12560
  | 7 => 12630
  | 8 => 12770
  | 9 => 12840
  | 10 => 18588
  | 11 => 18662
  | 12 => 24860
  | 13 => 24930
  | 14 => 25280
  | 15 => 25350
  | 16 => 25520
  | 17 => 25590
  | 18 => 25730
  | 19 => 25800
  | 20 => 37820
  | 21 => 37890
  | 22 => 38240
  | 23 => 38310
  | 24 => 38480
  | 25 => 38550
  | 26 => 38690
  | 27 => 38760
  | 28 => 44300
  | 29 => 44370
  | 30 => 44720
  | 31 => 44790
  | 32 => 44960
  | 33 => 45030
  | 34 => 45170
  | _ => 45240

def endE6Z (j : Fin 36) : Fin 6 → Fin 6 := allMaps6 (eidx6Z j)

/-- Indices of the other `46620`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6Z : Array Nat := #[
  0, 74, 11900, 11970, 12320, 12390, 12560, 12630, 12770, 12840, 18588, 18662, 24860, 24930,
  25280, 25350, 25520, 25590, 25730, 25800, 37820, 37890, 38240, 38310, 38480, 38550, 38690,
  38760, 44300, 44370, 44720, 44790, 44960, 45030, 45170, 45240]

def xarr6Z : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6Z.contains i)

def xidx6Z (j : Fin 46620) : Fin 46656 :=
  ⟨min (xarr6Z.getD j.1 0) 46655, by omega⟩

def endX6Z (j : Fin 46620) : Fin 6 → Fin 6 := allMaps6 (xidx6Z j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6Z` is given. -/
def uidx6Z : Fin 8 → Fin 36
  | 0 => 31
  | 1 => 23
  | 2 => 29
  | 3 => 21
  | 4 => 18
  | 5 => 8
  | 6 => 16
  | 7 => 6

theorem permE6Z_eq_endE6Z (i : Fin 8) : permE6Z i = endE6Z (uidx6Z i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `9`, so an invariant
operation is `9` values. -/
def rep6Z : Fin 9 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (1, 0)
  | 5 => (1, 1)
  | 6 => (1, 2)
  | 7 => (1, 3)
  | 8 => (1, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6Z : Fin 6 → Fin 6 → Fin 9 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (1, 2)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (4, 0)
  | 1, 1 => (5, 0)
  | 1, 2 => (6, 0)
  | 1, 3 => (7, 0)
  | 1, 4 => (8, 0)
  | 1, 5 => (8, 1)
  | 2, 0 => (2, 4)
  | 2, 1 => (3, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 5)
  | 2, 4 => (1, 4)
  | 2, 5 => (1, 6)
  | 3, 0 => (4, 2)
  | 3, 1 => (7, 2)
  | 3, 2 => (6, 2)
  | 3, 3 => (5, 2)
  | 3, 4 => (8, 2)
  | 3, 5 => (8, 3)
  | 4, 0 => (6, 4)
  | 4, 1 => (8, 4)
  | 4, 2 => (4, 4)
  | 4, 3 => (8, 5)
  | 4, 4 => (5, 4)
  | 4, 5 => (7, 4)
  | 5, 0 => (6, 6)
  | 5, 1 => (8, 6)
  | 5, 2 => (4, 6)
  | 5, 3 => (8, 7)
  | 5, 4 => (7, 6)
  | 5, 5 => (5, 6)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Z0 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6Z0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Z1 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Z1 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Z2 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6Z2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `2`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Z3 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 2
def val6Z3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Z4 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Z4 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Z5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Z5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Z6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Z6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Z7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Z7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `8`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6Z8 : Fin 1 → Fin 8
  | 0 => 0

/-- The `9` orbit values named by the family's arguments. -/
def dec6Z (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 9 → Fin 6
  | 0 => val6Z0 a
  | 1 => val6Z1 b
  | 2 => val6Z2 c
  | 3 => val6Z3 d
  | 4 => val6Z4 e
  | 5 => val6Z5 f
  | 6 => val6Z6 g
  | 7 => val6Z7 h
  | 8 => i

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6Z_eq_transport`). -/
def tab6Z (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6Z0 a
  | 0, 1 => val6Z1 b
  | 0, 2 => val6Z2 c
  | 0, 3 => pE6Z2 (val6Z1 b)
  | 0, 4 => val6Z3 d
  | 0, 5 => pE6Z1 (val6Z3 d)
  | 1, 0 => val6Z4 e
  | 1, 1 => val6Z5 f
  | 1, 2 => val6Z6 g
  | 1, 3 => val6Z7 h
  | 1, 4 => i
  | 1, 5 => pE6Z1 i
  | 2, 0 => pE6Z4 (val6Z2 c)
  | 2, 1 => pE6Z4 (val6Z3 d)
  | 2, 2 => pE6Z4 (val6Z0 a)
  | 2, 3 => pE6Z5 (val6Z3 d)
  | 2, 4 => pE6Z4 (val6Z1 b)
  | 2, 5 => pE6Z6 (val6Z1 b)
  | 3, 0 => pE6Z2 (val6Z4 e)
  | 3, 1 => pE6Z2 (val6Z7 h)
  | 3, 2 => pE6Z2 (val6Z6 g)
  | 3, 3 => pE6Z2 (val6Z5 f)
  | 3, 4 => pE6Z2 i
  | 3, 5 => pE6Z3 i
  | 4, 0 => pE6Z4 (val6Z6 g)
  | 4, 1 => pE6Z4 i
  | 4, 2 => pE6Z4 (val6Z4 e)
  | 4, 3 => pE6Z5 i
  | 4, 4 => pE6Z4 (val6Z5 f)
  | 4, 5 => pE6Z4 (val6Z7 h)
  | 5, 0 => pE6Z6 (val6Z6 g)
  | 5, 1 => pE6Z6 i
  | 5, 2 => pE6Z6 (val6Z4 e)
  | 5, 3 => pE6Z7 i
  | 5, 4 => pE6Z6 (val6Z7 h)
  | 5, 5 => pE6Z6 (val6Z5 f)

theorem tab6Z_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) :
    tab6Z a b c d e f g h i = Magma.transport permE6Z tr6Z (dec6Z a b c d e f g h i) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `98304` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6Z : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6Z 0 1 1 2 2 3 0 3 3
  | 1 => tab6Z 0 2 0 1 1 3 1 1 5
  | 2 => tab6Z 0 2 0 1 3 3 3 1 5
  | 3 => tab6Z 0 3 1 3 2 3 0 3 3

/-- The arguments as one mixed-radix index, which is how `rankIdx6Z` is addressed. -/
def encT6Z (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Nat :=
  a.1 * 49152 +
    b.1 * 12288 +
    c.1 * 6144 +
    d.1 * 1536 +
    e.1 * 384 +
    f.1 * 96 +
    g.1 * 24 +
    h.1 * 6 +
    i.1

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6Z` can name one
rather than search the list for it. The `98300` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6Z` excludes them. Read only by `native_decide`. -/
def rankIdx6Z : Nat → Nat
  | 22581 => 0
  | 26819 => 1
  | 27635 => 2
  | 48693 => 3
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6Z (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 4 :=
  ⟨min (rankIdx6Z (encT6Z a b c d e f g h i)) 3, by omega⟩


/-- `2` of the `36` demanded maps and `3` of the `46620` forbidden ones, enough to separate the `4`
members from the other `98300` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6Z` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6Z : Fin 2 → Fin 36
  | 0 => 1
  | 1 => 2
def x0idx6Z : Fin 3 → Fin 46620
  | 0 => 1
  | 1 => 442
  | 2 => 9329

def endE06Z (j : Fin 2) : Fin 6 → Fin 6 := endE6Z (e0idx6Z j)

def endX06Z (j : Fin 3) : Fin 6 → Fin 6 := endX6Z (x0idx6Z j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6Z (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6Z i)

theorem end6Z_isEndo (i : Fin 4) (j : Fin 36) : (end6Z i).IsEndo (endE6Z j) := by
  revert i j; native_decide

theorem end6Z_not_isEndo (i : Fin 4) (j : Fin 46620) : ¬ (end6Z i).IsEndo (endX6Z j) := by
  revert i j; native_decide

/-- `rank6Z` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6Z` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6Z (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6Z a b c d e f g h i) endE06Z endX06Z = true) :
    mem6Z (rank6Z a b c d e f g h i) = tab6Z a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6Z (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6Z a b c d e f g h i) endE06Z endX06Z = true) :
    ∃ idx, mem6Z idx = tab6Z a b c d e f g h i :=
  ⟨_, mem_rank6Z a b c d e f g h i hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6Z`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6Z` turns that into a member index. -/
theorem exists_end6Z {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6Z j))
    (hX : ∀ j, ¬ M.IsEndo (endX6Z j)) : ∃ i, end6Z i = M := by
  have hP : ∀ i, M.IsEndo (permE6Z i) := by
    intro i; rw [permE6Z_eq_endE6Z]; exact hE (uidx6Z i)
  have hop : M.op = Magma.transport permE6Z tr6Z (fun i ↦ M.op (rep6Z i).1 (rep6Z i).2) :=
    Magma.op_eq_transport (rep := rep6Z) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z0) (a := (rep6Z 0).1) (b := (rep6Z 0).2)
    (val := val6Z0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z1) (a := (rep6Z 1).1) (b := (rep6Z 1).2)
    (val := val6Z1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z2) (a := (rep6Z 2).1) (b := (rep6Z 2).2)
    (val := val6Z2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z3) (a := (rep6Z 3).1) (b := (rep6Z 3).2)
    (val := val6Z3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z4) (a := (rep6Z 4).1) (b := (rep6Z 4).2)
    (val := val6Z4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z5) (a := (rep6Z 5).1) (b := (rep6Z 5).2)
    (val := val6Z5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z6) (a := (rep6Z 6).1) (b := (rep6Z 6).2)
    (val := val6Z6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z7) (a := (rep6Z 7).1) (b := (rep6Z 7).2)
    (val := val6Z7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6Z) (idx := stabIdx6Z8) (a := (rep6Z 8).1) (b := (rep6Z 8).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6Z a b c d e f g h i = fun i ↦ M.op (rep6Z i).1 (rep6Z i).2 := by
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
  have key : tab6Z a b c d e f g h i = M.op := by
    rw [tab6Z_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6Z a b c d e f g h i) endE06Z endX06Z = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6Z j), fun j ↦ hX (x0idx6Z j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6Z a b c d e f g h i hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`36` monoid of `Magma.endE6Z`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6Z {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6Z i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6Z j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6Z i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6Z
    (fun k ↦ (Magma.end6Z_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6Z_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
