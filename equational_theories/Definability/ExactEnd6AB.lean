import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AB` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `68` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6AB0 : Fin 6 → Fin 6 := id
def pE6AB1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AB2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AB3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AB4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AB5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6AB6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6AB7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AB8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AB9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AB10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AB11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6AB : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6AB0
  | 1 => pE6AB1
  | 2 => pE6AB2
  | 3 => pE6AB3
  | 4 => pE6AB4
  | 5 => pE6AB5
  | 6 => pE6AB6
  | 7 => pE6AB7
  | 8 => pE6AB8
  | 9 => pE6AB9
  | 10 => pE6AB10
  | 11 => pE6AB11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `68` self-maps that must be endomorphisms: `002222`, `102222`, `012222`,
`112222`, `222222`, `332222`, `442222`, `552222`, `002332`, `102332`, `012332`, `112332`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AB : Fin 68 → Fin 46656
  | 0 => 18648
  | 1 => 18649
  | 2 => 18654
  | 3 => 18655
  | 4 => 18662
  | 5 => 18669
  | 6 => 18676
  | 7 => 18683
  | 8 => 20160
  | 9 => 20161
  | 10 => 20166
  | 11 => 20167
  | 12 => 21672
  | 13 => 21673
  | 14 => 21678
  | 15 => 21679
  | 16 => 23184
  | 17 => 23185
  | 18 => 23190
  | 19 => 23191
  | 20 => 26640
  | 21 => 26641
  | 22 => 26646
  | 23 => 26647
  | 24 => 27720
  | 25 => 27721
  | 26 => 27726
  | 27 => 27727
  | 28 => 29664
  | 29 => 29665
  | 30 => 29670
  | 31 => 29671
  | 32 => 30744
  | 33 => 30745
  | 34 => 30750
  | 35 => 30751
  | 36 => 34632
  | 37 => 34633
  | 38 => 34638
  | 39 => 34639
  | 40 => 36144
  | 41 => 36145
  | 42 => 36150
  | 43 => 36151
  | 44 => 36792
  | 45 => 36793
  | 46 => 36798
  | 47 => 36799
  | 48 => 38304
  | 49 => 38305
  | 50 => 38310
  | 51 => 38311
  | 52 => 42624
  | 53 => 42625
  | 54 => 42630
  | 55 => 42631
  | 56 => 43704
  | 57 => 43705
  | 58 => 43710
  | 59 => 43711
  | 60 => 44784
  | 61 => 44785
  | 62 => 44790
  | 63 => 44791
  | 64 => 45864
  | 65 => 45865
  | 66 => 45870
  | _ => 45871

def endE6AB (j : Fin 68) : Fin 6 → Fin 6 := allMaps6 (eidx6AB j)

/-- Indices of the other `46588`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AB : Array Nat := #[
  18648, 18649, 18654, 18655, 18662, 18669, 18676, 18683, 20160, 20161, 20166, 20167, 21672,
  21673, 21678, 21679, 23184, 23185, 23190, 23191, 26640, 26641, 26646, 26647, 27720, 27721,
  27726, 27727, 29664, 29665, 29670, 29671, 30744, 30745, 30750, 30751, 34632, 34633, 34638,
  34639, 36144, 36145, 36150, 36151, 36792, 36793, 36798, 36799, 38304, 38305, 38310, 38311,
  42624, 42625, 42630, 42631, 43704, 43705, 43710, 43711, 44784, 44785, 44790, 44791, 45864,
  45865, 45870, 45871]

def xarr6AB : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AB.contains i)

def xidx6AB (j : Fin 46588) : Fin 46656 :=
  ⟨min (xarr6AB.getD j.1 0) 46655, by omega⟩

def endX6AB (j : Fin 46588) : Fin 6 → Fin 6 := allMaps6 (xidx6AB j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AB` is given. -/
def uidx6AB : Fin 12 → Fin 68
  | 0 => 62
  | 1 => 50
  | 2 => 58
  | 3 => 34
  | 4 => 42
  | 5 => 30
  | 6 => 61
  | 7 => 49
  | 8 => 57
  | 9 => 33
  | 10 => 41
  | 11 => 29

theorem permE6AB_eq_endE6AB (i : Fin 12) : permE6AB i = endE6AB (uidx6AB i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6AB : Fin 11 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)
  | 4 => (2, 0)
  | 5 => (2, 2)
  | 6 => (2, 3)
  | 7 => (3, 0)
  | 8 => (3, 2)
  | 9 => (3, 3)
  | 10 => (3, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6AB : Fin 6 → Fin 6 → Fin 11 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (3, 2)
  | 0, 5 => (3, 4)
  | 1, 0 => (1, 6)
  | 1, 1 => (0, 6)
  | 1, 2 => (2, 6)
  | 1, 3 => (3, 6)
  | 1, 4 => (3, 8)
  | 1, 5 => (3, 10)
  | 2, 0 => (4, 0)
  | 2, 1 => (4, 6)
  | 2, 2 => (5, 0)
  | 2, 3 => (6, 0)
  | 2, 4 => (6, 2)
  | 2, 5 => (6, 4)
  | 3, 0 => (7, 0)
  | 3, 1 => (7, 6)
  | 3, 2 => (8, 0)
  | 3, 3 => (9, 0)
  | 3, 4 => (10, 0)
  | 3, 5 => (10, 1)
  | 4, 0 => (7, 2)
  | 4, 1 => (7, 8)
  | 4, 2 => (8, 2)
  | 4, 3 => (10, 2)
  | 4, 4 => (9, 2)
  | 4, 5 => (10, 3)
  | 5, 0 => (7, 4)
  | 5, 1 => (7, 10)
  | 5, 2 => (8, 4)
  | 5, 3 => (10, 4)
  | 5, 4 => (10, 5)
  | 5, 5 => (9, 4)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AB0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AB0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AB1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AB1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AB2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AB2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AB3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AB3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AB4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AB4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6AB5 : Fin 12 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 10
  | 11 => 11
def val6AB5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AB6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AB6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AB7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AB7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AB8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AB8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AB9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AB9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AB10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6AB10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6AB (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6AB0 a
  | 1 => val6AB1 b
  | 2 => val6AB2 c
  | 3 => val6AB3 d
  | 4 => val6AB4 e
  | 5 => val6AB5 f
  | 6 => val6AB6 g
  | 7 => val6AB7 h
  | 8 => val6AB8 i
  | 9 => val6AB9 j
  | 10 => val6AB10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AB_eq_transport`). -/
def tab6AB (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AB0 a
  | 0, 1 => val6AB1 b
  | 0, 2 => val6AB2 c
  | 0, 3 => val6AB3 d
  | 0, 4 => pE6AB2 (val6AB3 d)
  | 0, 5 => pE6AB4 (val6AB3 d)
  | 1, 0 => pE6AB6 (val6AB1 b)
  | 1, 1 => pE6AB6 (val6AB0 a)
  | 1, 2 => pE6AB6 (val6AB2 c)
  | 1, 3 => pE6AB6 (val6AB3 d)
  | 1, 4 => pE6AB8 (val6AB3 d)
  | 1, 5 => pE6AB10 (val6AB3 d)
  | 2, 0 => val6AB4 e
  | 2, 1 => pE6AB6 (val6AB4 e)
  | 2, 2 => val6AB5 f
  | 2, 3 => val6AB6 g
  | 2, 4 => pE6AB2 (val6AB6 g)
  | 2, 5 => pE6AB4 (val6AB6 g)
  | 3, 0 => val6AB7 h
  | 3, 1 => pE6AB6 (val6AB7 h)
  | 3, 2 => val6AB8 i
  | 3, 3 => val6AB9 j
  | 3, 4 => val6AB10 k
  | 3, 5 => pE6AB1 (val6AB10 k)
  | 4, 0 => pE6AB2 (val6AB7 h)
  | 4, 1 => pE6AB8 (val6AB7 h)
  | 4, 2 => pE6AB2 (val6AB8 i)
  | 4, 3 => pE6AB2 (val6AB10 k)
  | 4, 4 => pE6AB2 (val6AB9 j)
  | 4, 5 => pE6AB3 (val6AB10 k)
  | 5, 0 => pE6AB4 (val6AB7 h)
  | 5, 1 => pE6AB10 (val6AB7 h)
  | 5, 2 => pE6AB4 (val6AB8 i)
  | 5, 3 => pE6AB4 (val6AB10 k)
  | 5, 4 => pE6AB5 (val6AB10 k)
  | 5, 5 => pE6AB4 (val6AB9 j)

theorem tab6AB_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6AB a b c d e f g h i j k = Magma.transport permE6AB tr6AB (dec6AB a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `1` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AB : Fin 1 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AB 2 2 0 0 0 0 1 0 1 0 3

/-- The arguments as one mixed-radix index, which is how `rankIdx6AB` is addressed. -/
def encT6AB (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4) : Nat :=
  a.1 * 13824 +
    b.1 * 4608 +
    c.1 * 1536 +
    d.1 * 384 +
    e.1 * 128 +
    f.1 * 128 +
    g.1 * 64 +
    h.1 * 16 +
    i.1 * 8 +
    j.1 * 4 +
    k.1

/-- Which of the `1` members a given invariant tuple is, so that `mem_of_isExact6AB` can name one
rather than search the list for it. The `41471` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6AB` excludes them. Read only by `native_decide`. -/
def rankIdx6AB : Nat → Nat
  | 36939 => 0
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AB (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4) : Fin 1 :=
  ⟨min (rankIdx6AB (encT6AB a b c d e f g h i j k)) 0, by omega⟩


/-- `2` of the `68` demanded maps and `1` of the `46588` forbidden ones, enough to separate the `1`
members from the other `41471` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AB` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AB : Fin 2 → Fin 68
  | 0 => 5
  | 1 => 8
def x0idx6AB : Fin 1 → Fin 46588
  | 0 => 18856

def endE06AB (j : Fin 2) : Fin 6 → Fin 6 := endE6AB (e0idx6AB j)

def endX06AB (j : Fin 1) : Fin 6 → Fin 6 := endX6AB (x0idx6AB j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AB (i : Fin 1) : Magma (Fin 6) := Magma.mk (mem6AB i)

theorem end6AB_isEndo (i : Fin 1) (j : Fin 68) : (end6AB i).IsEndo (endE6AB j) := by
  revert i j; native_decide

theorem end6AB_not_isEndo (i : Fin 1) (j : Fin 46588) : ¬ (end6AB i).IsEndo (endX6AB j) := by
  revert i j; native_decide

/-- `rank6AB` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AB` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AB (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AB a b c d e f g h i j k) endE06AB endX06AB = true) :
    mem6AB (rank6AB a b c d e f g h i j k) = tab6AB a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `1` listed
members. -/
theorem mem_of_isExact6AB (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AB a b c d e f g h i j k) endE06AB endX06AB = true) :
    ∃ idx, mem6AB idx = tab6AB a b c d e f g h i j k :=
  ⟨_, mem_rank6AB a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AB`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AB` turns that into a member index. -/
theorem exists_end6AB {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AB j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AB j)) : ∃ i, end6AB i = M := by
  have hP : ∀ i, M.IsEndo (permE6AB i) := by
    intro i; rw [permE6AB_eq_endE6AB]; exact hE (uidx6AB i)
  have hop : M.op = Magma.transport permE6AB tr6AB (fun i ↦ M.op (rep6AB i).1 (rep6AB i).2) :=
    Magma.op_eq_transport (rep := rep6AB) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB0) (a := (rep6AB 0).1) (b := (rep6AB 0).2)
    (val := val6AB0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB1) (a := (rep6AB 1).1) (b := (rep6AB 1).2)
    (val := val6AB1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB2) (a := (rep6AB 2).1) (b := (rep6AB 2).2)
    (val := val6AB2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB3) (a := (rep6AB 3).1) (b := (rep6AB 3).2)
    (val := val6AB3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB4) (a := (rep6AB 4).1) (b := (rep6AB 4).2)
    (val := val6AB4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB5) (a := (rep6AB 5).1) (b := (rep6AB 5).2)
    (val := val6AB5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB6) (a := (rep6AB 6).1) (b := (rep6AB 6).2)
    (val := val6AB6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB7) (a := (rep6AB 7).1) (b := (rep6AB 7).2)
    (val := val6AB7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB8) (a := (rep6AB 8).1) (b := (rep6AB 8).2)
    (val := val6AB8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB9) (a := (rep6AB 9).1) (b := (rep6AB 9).2)
    (val := val6AB9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6AB) (idx := stabIdx6AB10) (a := (rep6AB 10).1) (b := (rep6AB 10).2)
    (val := val6AB10) hP (by decide) (by decide)
  have hdec : dec6AB a b c d e f g h i j k = fun i ↦ M.op (rep6AB i).1 (rep6AB i).2 := by
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
  have key : tab6AB a b c d e f g h i j k = M.op := by
    rw [tab6AB_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AB a b c d e f g h i j k) endE06AB endX06AB = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AB j), fun j ↦ hX (x0idx6AB j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AB a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`68` monoid of `Magma.endE6AB`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AB {L L' : Law.NatMagmaLaw} {i : Fin 1}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AB i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AB j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AB i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AB
    (fun k ↦ (Magma.end6AB_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AB_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
