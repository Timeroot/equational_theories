import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `R` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `52` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6R0 : Fin 6 → Fin 6 := id
def pE6R1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6R2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6R3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6R4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6R5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6R6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6R7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6R8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6R9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6R10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6R11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6R : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6R0
  | 1 => pE6R1
  | 2 => pE6R2
  | 3 => pE6R3
  | 4 => pE6R4
  | 5 => pE6R5
  | 6 => pE6R6
  | 7 => pE6R7
  | 8 => pE6R8
  | 9 => pE6R9
  | 10 => pE6R10
  | 11 => pE6R11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `52` self-maps that must be endomorphisms: `102222`, `202222`, `012222`,
`212222`, `022222`, `122222`, `222222`, `333333`, `102543`, `202543`, `012543`, `212543`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6R : Fin 52 → Fin 46656
  | 0 => 18649
  | 1 => 18650
  | 2 => 18654
  | 3 => 18656
  | 4 => 18660
  | 5 => 18661
  | 6 => 18662
  | 7 => 27993
  | 8 => 29665
  | 9 => 29666
  | 10 => 29670
  | 11 => 29672
  | 12 => 29676
  | 13 => 29677
  | 14 => 29678
  | 15 => 30745
  | 16 => 30746
  | 17 => 30750
  | 18 => 30752
  | 19 => 30756
  | 20 => 30757
  | 21 => 30758
  | 22 => 36145
  | 23 => 36146
  | 24 => 36150
  | 25 => 36152
  | 26 => 36156
  | 27 => 36157
  | 28 => 36158
  | 29 => 37324
  | 30 => 38305
  | 31 => 38306
  | 32 => 38310
  | 33 => 38312
  | 34 => 38316
  | 35 => 38317
  | 36 => 38318
  | 37 => 43705
  | 38 => 43706
  | 39 => 43710
  | 40 => 43712
  | 41 => 43716
  | 42 => 43717
  | 43 => 43718
  | 44 => 44785
  | 45 => 44786
  | 46 => 44790
  | 47 => 44792
  | 48 => 44796
  | 49 => 44797
  | 50 => 44798
  | _ => 46655

def endE6R (j : Fin 52) : Fin 6 → Fin 6 := allMaps6 (eidx6R j)

/-- Indices of the other `46604`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6R : Array Nat := #[
  18649, 18650, 18654, 18656, 18660, 18661, 18662, 27993, 29665, 29666, 29670, 29672, 29676,
  29677, 29678, 30745, 30746, 30750, 30752, 30756, 30757, 30758, 36145, 36146, 36150, 36152,
  36156, 36157, 36158, 37324, 38305, 38306, 38310, 38312, 38316, 38317, 38318, 43705, 43706,
  43710, 43712, 43716, 43717, 43718, 44785, 44786, 44790, 44792, 44796, 44797, 44798, 46655]

def xarr6R : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6R.contains i)

def xidx6R (j : Fin 46604) : Fin 46656 :=
  ⟨min (xarr6R.getD j.1 0) 46655, by omega⟩

def endX6R (j : Fin 46604) : Fin 6 → Fin 6 := allMaps6 (xidx6R j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6R` is given. -/
def uidx6R : Fin 12 → Fin 52
  | 0 => 46
  | 1 => 32
  | 2 => 39
  | 3 => 17
  | 4 => 24
  | 5 => 10
  | 6 => 44
  | 7 => 30
  | 8 => 37
  | 9 => 15
  | 10 => 22
  | 11 => 8

theorem permE6R_eq_endE6R (i : Fin 12) : permE6R i = endE6R (uidx6R i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6R : Fin 11 → Fin 6 × Fin 6
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
def tr6R : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6R0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6R0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6R1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6R1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6R2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6R2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6R3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6R3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6R4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6R4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6R5 : Fin 12 → Fin 12
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
def val6R5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6R6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6R6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6R7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6R7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6R8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6R8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6R9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6R9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6R10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6R10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6R (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6R0 a
  | 1 => val6R1 b
  | 2 => val6R2 c
  | 3 => val6R3 d
  | 4 => val6R4 e
  | 5 => val6R5 f
  | 6 => val6R6 g
  | 7 => val6R7 h
  | 8 => val6R8 i
  | 9 => val6R9 j
  | 10 => val6R10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6R_eq_transport`). -/
def tab6R (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6R0 a
  | 0, 1 => val6R1 b
  | 0, 2 => val6R2 c
  | 0, 3 => val6R3 d
  | 0, 4 => pE6R2 (val6R3 d)
  | 0, 5 => pE6R4 (val6R3 d)
  | 1, 0 => pE6R6 (val6R1 b)
  | 1, 1 => pE6R6 (val6R0 a)
  | 1, 2 => pE6R6 (val6R2 c)
  | 1, 3 => pE6R6 (val6R3 d)
  | 1, 4 => pE6R8 (val6R3 d)
  | 1, 5 => pE6R10 (val6R3 d)
  | 2, 0 => val6R4 e
  | 2, 1 => pE6R6 (val6R4 e)
  | 2, 2 => val6R5 f
  | 2, 3 => val6R6 g
  | 2, 4 => pE6R2 (val6R6 g)
  | 2, 5 => pE6R4 (val6R6 g)
  | 3, 0 => val6R7 h
  | 3, 1 => pE6R6 (val6R7 h)
  | 3, 2 => val6R8 i
  | 3, 3 => val6R9 j
  | 3, 4 => val6R10 k
  | 3, 5 => pE6R1 (val6R10 k)
  | 4, 0 => pE6R2 (val6R7 h)
  | 4, 1 => pE6R8 (val6R7 h)
  | 4, 2 => pE6R2 (val6R8 i)
  | 4, 3 => pE6R2 (val6R10 k)
  | 4, 4 => pE6R2 (val6R9 j)
  | 4, 5 => pE6R3 (val6R10 k)
  | 5, 0 => pE6R4 (val6R7 h)
  | 5, 1 => pE6R10 (val6R7 h)
  | 5, 2 => pE6R4 (val6R8 i)
  | 5, 3 => pE6R4 (val6R10 k)
  | 5, 4 => pE6R5 (val6R10 k)
  | 5, 5 => pE6R4 (val6R9 j)

theorem tab6R_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6R a b c d e f g h i j k = Magma.transport permE6R tr6R (dec6R a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6R : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6R 2 0 0 0 2 0 0 3 1 1 0
  | 1 => tab6R 2 1 2 3 0 0 1 0 0 1 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6R` is addressed. -/
def encT6R (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Nat :=
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

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6R` can name one
rather than search the list for it. The `41470` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6R` excludes them. Read only by `native_decide`. -/
def rankIdx6R : Nat → Nat
  | 27964 => 0
  | 36548 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6R (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 2 :=
  ⟨min (rankIdx6R (encT6R a b c d e f g h i j k)) 1, by omega⟩


/-- `3` of the `52` demanded maps and `4` of the `46604` forbidden ones, enough to separate the `2`
members from the other `41470` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6R` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6R : Fin 3 → Fin 52
  | 0 => 0
  | 1 => 7
  | 2 => 9
def x0idx6R : Fin 4 → Fin 46604
  | 0 => 0
  | 1 => 18648
  | 2 => 18858
  | 3 => 27930

def endE06R (j : Fin 3) : Fin 6 → Fin 6 := endE6R (e0idx6R j)

def endX06R (j : Fin 4) : Fin 6 → Fin 6 := endX6R (x0idx6R j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6R (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6R i)

theorem end6R_isEndo (i : Fin 2) (j : Fin 52) : (end6R i).IsEndo (endE6R j) := by
  revert i j; native_decide

theorem end6R_not_isEndo (i : Fin 2) (j : Fin 46604) : ¬ (end6R i).IsEndo (endX6R j) := by
  revert i j; native_decide

/-- `rank6R` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6R` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6R (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6R a b c d e f g h i j k) endE06R endX06R = true) :
    mem6R (rank6R a b c d e f g h i j k) = tab6R a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6R (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6R a b c d e f g h i j k) endE06R endX06R = true) :
    ∃ idx, mem6R idx = tab6R a b c d e f g h i j k :=
  ⟨_, mem_rank6R a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6R`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6R` turns that into a member index. -/
theorem exists_end6R {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6R j))
    (hX : ∀ j, ¬ M.IsEndo (endX6R j)) : ∃ i, end6R i = M := by
  have hP : ∀ i, M.IsEndo (permE6R i) := by
    intro i; rw [permE6R_eq_endE6R]; exact hE (uidx6R i)
  have hop : M.op = Magma.transport permE6R tr6R (fun i ↦ M.op (rep6R i).1 (rep6R i).2) :=
    Magma.op_eq_transport (rep := rep6R) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R0) (a := (rep6R 0).1) (b := (rep6R 0).2)
    (val := val6R0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R1) (a := (rep6R 1).1) (b := (rep6R 1).2)
    (val := val6R1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R2) (a := (rep6R 2).1) (b := (rep6R 2).2)
    (val := val6R2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R3) (a := (rep6R 3).1) (b := (rep6R 3).2)
    (val := val6R3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R4) (a := (rep6R 4).1) (b := (rep6R 4).2)
    (val := val6R4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R5) (a := (rep6R 5).1) (b := (rep6R 5).2)
    (val := val6R5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R6) (a := (rep6R 6).1) (b := (rep6R 6).2)
    (val := val6R6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R7) (a := (rep6R 7).1) (b := (rep6R 7).2)
    (val := val6R7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R8) (a := (rep6R 8).1) (b := (rep6R 8).2)
    (val := val6R8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R9) (a := (rep6R 9).1) (b := (rep6R 9).2)
    (val := val6R9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6R) (idx := stabIdx6R10) (a := (rep6R 10).1) (b := (rep6R 10).2)
    (val := val6R10) hP (by decide) (by decide)
  have hdec : dec6R a b c d e f g h i j k = fun i ↦ M.op (rep6R i).1 (rep6R i).2 := by
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
  have key : tab6R a b c d e f g h i j k = M.op := by
    rw [tab6R_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6R a b c d e f g h i j k) endE06R endX06R = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6R j), fun j ↦ hX (x0idx6R j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6R a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`52` monoid of `Magma.endE6R`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6R {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6R i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6R j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6R i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6R
    (fun k ↦ (Magma.end6R_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6R_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
