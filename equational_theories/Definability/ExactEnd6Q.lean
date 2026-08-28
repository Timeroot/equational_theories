import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `Q` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `70` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6Q0 : Fin 6 → Fin 6 := id
def pE6Q1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6Q2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6Q3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6Q4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6Q5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6Q6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6Q7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6Q8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6Q9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6Q10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6Q11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6Q : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6Q0
  | 1 => pE6Q1
  | 2 => pE6Q2
  | 3 => pE6Q3
  | 4 => pE6Q4
  | 5 => pE6Q5
  | 6 => pE6Q6
  | 7 => pE6Q7
  | 8 => pE6Q8
  | 9 => pE6Q9
  | 10 => pE6Q10
  | 11 => pE6Q11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `70` self-maps that must be endomorphisms: `222222`, `222322`, `222422`,
`222522`, `222232`, `222432`, `222532`, `222242`, `222342`, `222542`, `222252`, `222352`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6Q : Fin 70 → Fin 46656
  | 0 => 18662
  | 1 => 18878
  | 2 => 19094
  | 3 => 19310
  | 4 => 19958
  | 5 => 20390
  | 6 => 20606
  | 7 => 21254
  | 8 => 21470
  | 9 => 21902
  | 10 => 22550
  | 11 => 22766
  | 12 => 22982
  | 13 => 26438
  | 14 => 26870
  | 15 => 27086
  | 16 => 29030
  | 17 => 29665
  | 18 => 29666
  | 19 => 29670
  | 20 => 29672
  | 21 => 29676
  | 22 => 29677
  | 23 => 29678
  | 24 => 30326
  | 25 => 30745
  | 26 => 30746
  | 27 => 30750
  | 28 => 30752
  | 29 => 30756
  | 30 => 30757
  | 31 => 30758
  | 32 => 34214
  | 33 => 34430
  | 34 => 34862
  | 35 => 35510
  | 36 => 36145
  | 37 => 36146
  | 38 => 36150
  | 39 => 36152
  | 40 => 36156
  | 41 => 36157
  | 42 => 36158
  | 43 => 38102
  | 44 => 38305
  | 45 => 38306
  | 46 => 38310
  | 47 => 38312
  | 48 => 38316
  | 49 => 38317
  | 50 => 38318
  | 51 => 41990
  | 52 => 42206
  | 53 => 42422
  | 54 => 43286
  | 55 => 43705
  | 56 => 43706
  | 57 => 43710
  | 58 => 43712
  | 59 => 43716
  | 60 => 43717
  | 61 => 43718
  | 62 => 44582
  | 63 => 44785
  | 64 => 44786
  | 65 => 44790
  | 66 => 44792
  | 67 => 44796
  | 68 => 44797
  | _ => 44798

def endE6Q (j : Fin 70) : Fin 6 → Fin 6 := allMaps6 (eidx6Q j)

/-- Indices of the other `46586`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6Q : Array Nat := #[
  18662, 18878, 19094, 19310, 19958, 20390, 20606, 21254, 21470, 21902, 22550, 22766, 22982,
  26438, 26870, 27086, 29030, 29665, 29666, 29670, 29672, 29676, 29677, 29678, 30326, 30745,
  30746, 30750, 30752, 30756, 30757, 30758, 34214, 34430, 34862, 35510, 36145, 36146, 36150,
  36152, 36156, 36157, 36158, 38102, 38305, 38306, 38310, 38312, 38316, 38317, 38318, 41990,
  42206, 42422, 43286, 43705, 43706, 43710, 43712, 43716, 43717, 43718, 44582, 44785, 44786,
  44790, 44792, 44796, 44797, 44798]

def xarr6Q : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6Q.contains i)

def xidx6Q (j : Fin 46586) : Fin 46656 :=
  ⟨min (xarr6Q.getD j.1 0) 46655, by omega⟩

def endX6Q (j : Fin 46586) : Fin 6 → Fin 6 := allMaps6 (xidx6Q j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6Q` is given. -/
def uidx6Q : Fin 12 → Fin 70
  | 0 => 65
  | 1 => 46
  | 2 => 57
  | 3 => 27
  | 4 => 38
  | 5 => 19
  | 6 => 63
  | 7 => 44
  | 8 => 55
  | 9 => 25
  | 10 => 36
  | 11 => 17

theorem permE6Q_eq_endE6Q (i : Fin 12) : permE6Q i = endE6Q (uidx6Q i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6Q : Fin 11 → Fin 6 × Fin 6
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
def tr6Q : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6Q0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6Q0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6Q1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6Q1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6Q2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6Q2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Q3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6Q3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6Q4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6Q4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6Q5 : Fin 12 → Fin 12
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
def val6Q5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Q6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6Q6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Q7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6Q7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Q8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6Q8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Q9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6Q9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Q10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6Q10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6Q (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6Q0 a
  | 1 => val6Q1 b
  | 2 => val6Q2 c
  | 3 => val6Q3 d
  | 4 => val6Q4 e
  | 5 => val6Q5 f
  | 6 => val6Q6 g
  | 7 => val6Q7 h
  | 8 => val6Q8 i
  | 9 => val6Q9 j
  | 10 => val6Q10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6Q_eq_transport`). -/
def tab6Q (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6Q0 a
  | 0, 1 => val6Q1 b
  | 0, 2 => val6Q2 c
  | 0, 3 => val6Q3 d
  | 0, 4 => pE6Q2 (val6Q3 d)
  | 0, 5 => pE6Q4 (val6Q3 d)
  | 1, 0 => pE6Q6 (val6Q1 b)
  | 1, 1 => pE6Q6 (val6Q0 a)
  | 1, 2 => pE6Q6 (val6Q2 c)
  | 1, 3 => pE6Q6 (val6Q3 d)
  | 1, 4 => pE6Q8 (val6Q3 d)
  | 1, 5 => pE6Q10 (val6Q3 d)
  | 2, 0 => val6Q4 e
  | 2, 1 => pE6Q6 (val6Q4 e)
  | 2, 2 => val6Q5 f
  | 2, 3 => val6Q6 g
  | 2, 4 => pE6Q2 (val6Q6 g)
  | 2, 5 => pE6Q4 (val6Q6 g)
  | 3, 0 => val6Q7 h
  | 3, 1 => pE6Q6 (val6Q7 h)
  | 3, 2 => val6Q8 i
  | 3, 3 => val6Q9 j
  | 3, 4 => val6Q10 k
  | 3, 5 => pE6Q1 (val6Q10 k)
  | 4, 0 => pE6Q2 (val6Q7 h)
  | 4, 1 => pE6Q8 (val6Q7 h)
  | 4, 2 => pE6Q2 (val6Q8 i)
  | 4, 3 => pE6Q2 (val6Q10 k)
  | 4, 4 => pE6Q2 (val6Q9 j)
  | 4, 5 => pE6Q3 (val6Q10 k)
  | 5, 0 => pE6Q4 (val6Q7 h)
  | 5, 1 => pE6Q10 (val6Q7 h)
  | 5, 2 => pE6Q4 (val6Q8 i)
  | 5, 3 => pE6Q4 (val6Q10 k)
  | 5, 4 => pE6Q5 (val6Q10 k)
  | 5, 5 => pE6Q4 (val6Q9 j)

theorem tab6Q_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6Q a b c d e f g h i j k = Magma.transport permE6Q tr6Q (dec6Q a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6Q : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6Q 2 0 0 3 2 0 1 0 0 0 2
  | 1 => tab6Q 2 0 0 3 2 0 1 2 0 0 2
  | 2 => tab6Q 2 1 2 0 0 0 0 3 1 0 1
  | 3 => tab6Q 2 1 2 2 0 0 0 3 1 0 1

/-- The arguments as one mixed-radix index, which is how `rankIdx6Q` is addressed. -/
def encT6Q (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
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

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6Q` can name one
rather than search the list for it. The `41468` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6Q` excludes them. Read only by `native_decide`. -/
def rankIdx6Q : Nat → Nat
  | 29122 => 0
  | 29154 => 1
  | 35385 => 2
  | 36153 => 3
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6Q (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 4 :=
  ⟨min (rankIdx6Q (encT6Q a b c d e f g h i j k)) 3, by omega⟩


/-- `2` of the `70` demanded maps and `5` of the `46586` forbidden ones, enough to separate the `4`
members from the other `41468` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6Q` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6Q : Fin 2 → Fin 70
  | 0 => 1
  | 1 => 18
def x0idx6Q : Fin 5 → Fin 46586
  | 0 => 0
  | 1 => 1814
  | 2 => 20169
  | 3 => 27977
  | 4 => 29647

def endE06Q (j : Fin 2) : Fin 6 → Fin 6 := endE6Q (e0idx6Q j)

def endX06Q (j : Fin 5) : Fin 6 → Fin 6 := endX6Q (x0idx6Q j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6Q (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6Q i)

theorem end6Q_isEndo (i : Fin 4) (j : Fin 70) : (end6Q i).IsEndo (endE6Q j) := by
  revert i j; native_decide

theorem end6Q_not_isEndo (i : Fin 4) (j : Fin 46586) : ¬ (end6Q i).IsEndo (endX6Q j) := by
  revert i j; native_decide

/-- `rank6Q` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6Q` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6Q (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6Q a b c d e f g h i j k) endE06Q endX06Q = true) :
    mem6Q (rank6Q a b c d e f g h i j k) = tab6Q a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6Q (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6Q a b c d e f g h i j k) endE06Q endX06Q = true) :
    ∃ idx, mem6Q idx = tab6Q a b c d e f g h i j k :=
  ⟨_, mem_rank6Q a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6Q`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6Q` turns that into a member index. -/
theorem exists_end6Q {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6Q j))
    (hX : ∀ j, ¬ M.IsEndo (endX6Q j)) : ∃ i, end6Q i = M := by
  have hP : ∀ i, M.IsEndo (permE6Q i) := by
    intro i; rw [permE6Q_eq_endE6Q]; exact hE (uidx6Q i)
  have hop : M.op = Magma.transport permE6Q tr6Q (fun i ↦ M.op (rep6Q i).1 (rep6Q i).2) :=
    Magma.op_eq_transport (rep := rep6Q) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q0) (a := (rep6Q 0).1) (b := (rep6Q 0).2)
    (val := val6Q0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q1) (a := (rep6Q 1).1) (b := (rep6Q 1).2)
    (val := val6Q1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q2) (a := (rep6Q 2).1) (b := (rep6Q 2).2)
    (val := val6Q2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q3) (a := (rep6Q 3).1) (b := (rep6Q 3).2)
    (val := val6Q3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q4) (a := (rep6Q 4).1) (b := (rep6Q 4).2)
    (val := val6Q4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q5) (a := (rep6Q 5).1) (b := (rep6Q 5).2)
    (val := val6Q5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q6) (a := (rep6Q 6).1) (b := (rep6Q 6).2)
    (val := val6Q6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q7) (a := (rep6Q 7).1) (b := (rep6Q 7).2)
    (val := val6Q7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q8) (a := (rep6Q 8).1) (b := (rep6Q 8).2)
    (val := val6Q8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q9) (a := (rep6Q 9).1) (b := (rep6Q 9).2)
    (val := val6Q9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6Q) (idx := stabIdx6Q10) (a := (rep6Q 10).1) (b := (rep6Q 10).2)
    (val := val6Q10) hP (by decide) (by decide)
  have hdec : dec6Q a b c d e f g h i j k = fun i ↦ M.op (rep6Q i).1 (rep6Q i).2 := by
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
  have key : tab6Q a b c d e f g h i j k = M.op := by
    rw [tab6Q_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6Q a b c d e f g h i j k) endE06Q endX06Q = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6Q j), fun j ↦ hX (x0idx6Q j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6Q a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`70` monoid of `Magma.endE6Q`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6Q {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6Q i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6Q j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6Q i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6Q
    (fun k ↦ (Magma.end6Q_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6Q_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
