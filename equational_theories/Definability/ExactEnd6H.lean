import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `H` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 2)(1 4)(3 5), (0 2)(1 4 3 5)⟩`

`End(M)` is `70` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `9` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(1 3)`, `(1 3)(4 5)`, `(0 2)(1 4)(3 5)`, `(0 2)(1
4 3 5)`, `(0 2)(1 5 3 4)`, `(0 2)(1 5)(3 4)`. -/
def pE6H0 : Fin 6 → Fin 6 := id
def pE6H1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6H2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5
def pE6H3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4
def pE6H4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 3
def pE6H5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 1
def pE6H6 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 3
def pE6H7 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1

def permE6H : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6H0
  | 1 => pE6H1
  | 2 => pE6H2
  | 3 => pE6H3
  | 4 => pE6H4
  | 5 => pE6H5
  | 6 => pE6H6
  | 7 => pE6H7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `70` self-maps that must be endomorphisms: `000000`, `040000`, `050000`,
`000400`, `040400`, `000500`, `050500`, `000040`, `040040`, `000440`, `040440`, `000050`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6H : Fin 70 → Fin 46656
  | 0 => 0
  | 1 => 24
  | 2 => 30
  | 3 => 864
  | 4 => 888
  | 5 => 1080
  | 6 => 1110
  | 7 => 5184
  | 8 => 5208
  | 9 => 6048
  | 10 => 6072
  | 11 => 6480
  | 12 => 6510
  | 13 => 7560
  | 14 => 7590
  | 15 => 9368
  | 16 => 9374
  | 17 => 9584
  | 18 => 9590
  | 19 => 10664
  | 20 => 10670
  | 21 => 10880
  | 22 => 10886
  | 23 => 12560
  | 24 => 12770
  | 25 => 17144
  | 26 => 17150
  | 27 => 17360
  | 28 => 17366
  | 29 => 18440
  | 30 => 18446
  | 31 => 18656
  | 32 => 18662
  | 33 => 18668
  | 34 => 18878
  | 35 => 18884
  | 36 => 19958
  | 37 => 19964
  | 38 => 20174
  | 39 => 20180
  | 40 => 25520
  | 41 => 25730
  | 42 => 26438
  | 43 => 26444
  | 44 => 26654
  | 45 => 26660
  | 46 => 27734
  | 47 => 27740
  | 48 => 27950
  | 49 => 27956
  | 50 => 31104
  | 51 => 31128
  | 52 => 31968
  | 53 => 31992
  | 54 => 36288
  | 55 => 36312
  | 56 => 37152
  | 57 => 37176
  | 58 => 37890
  | 59 => 38310
  | 60 => 38880
  | 61 => 38910
  | 62 => 39960
  | 63 => 39990
  | 64 => 44370
  | 65 => 44790
  | 66 => 45360
  | 67 => 45390
  | 68 => 46440
  | _ => 46470

def endE6H (j : Fin 70) : Fin 6 → Fin 6 := allMaps6 (eidx6H j)

/-- Indices of the other `46586`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6H : Array Nat := #[
  0, 24, 30, 864, 888, 1080, 1110, 5184, 5208, 6048, 6072, 6480, 6510, 7560, 7590, 9368, 9374,
  9584, 9590, 10664, 10670, 10880, 10886, 12560, 12770, 17144, 17150, 17360, 17366, 18440, 18446,
  18656, 18662, 18668, 18878, 18884, 19958, 19964, 20174, 20180, 25520, 25730, 26438, 26444,
  26654, 26660, 27734, 27740, 27950, 27956, 31104, 31128, 31968, 31992, 36288, 36312, 37152,
  37176, 37890, 38310, 38880, 38910, 39960, 39990, 44370, 44790, 45360, 45390, 46440, 46470]

def xarr6H : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6H.contains i)

def xidx6H (j : Fin 46586) : Fin 46656 :=
  ⟨min (xarr6H.getD j.1 0) 46655, by omega⟩

def endX6H (j : Fin 46586) : Fin 6 → Fin 6 := allMaps6 (xidx6H j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6H` is given. -/
def uidx6H : Fin 8 → Fin 70
  | 0 => 65
  | 1 => 59
  | 2 => 64
  | 3 => 58
  | 4 => 41
  | 5 => 24
  | 6 => 40
  | 7 => 23

theorem permE6H_eq_endE6H (i : Fin 8) : permE6H i = endE6H (uidx6H i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `9`, so an invariant
operation is `9` values. -/
def rep6H : Fin 9 → Fin 6 × Fin 6
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
def tr6H : Fin 6 → Fin 6 → Fin 9 × Fin 8
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
def stabIdx6H0 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6H0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6H1 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6H1 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6H2 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6H2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `2`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6H3 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 2
def val6H3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6H4 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6H4 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6H5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6H5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6H6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6H6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6H7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6H7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `8`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6H8 : Fin 1 → Fin 8
  | 0 => 0

/-- The `9` orbit values named by the family's arguments. -/
def dec6H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 9 → Fin 6
  | 0 => val6H0 a
  | 1 => val6H1 b
  | 2 => val6H2 c
  | 3 => val6H3 d
  | 4 => val6H4 e
  | 5 => val6H5 f
  | 6 => val6H6 g
  | 7 => val6H7 h
  | 8 => i

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6H_eq_transport`). -/
def tab6H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6H0 a
  | 0, 1 => val6H1 b
  | 0, 2 => val6H2 c
  | 0, 3 => pE6H2 (val6H1 b)
  | 0, 4 => val6H3 d
  | 0, 5 => pE6H1 (val6H3 d)
  | 1, 0 => val6H4 e
  | 1, 1 => val6H5 f
  | 1, 2 => val6H6 g
  | 1, 3 => val6H7 h
  | 1, 4 => i
  | 1, 5 => pE6H1 i
  | 2, 0 => pE6H4 (val6H2 c)
  | 2, 1 => pE6H4 (val6H3 d)
  | 2, 2 => pE6H4 (val6H0 a)
  | 2, 3 => pE6H5 (val6H3 d)
  | 2, 4 => pE6H4 (val6H1 b)
  | 2, 5 => pE6H6 (val6H1 b)
  | 3, 0 => pE6H2 (val6H4 e)
  | 3, 1 => pE6H2 (val6H7 h)
  | 3, 2 => pE6H2 (val6H6 g)
  | 3, 3 => pE6H2 (val6H5 f)
  | 3, 4 => pE6H2 i
  | 3, 5 => pE6H3 i
  | 4, 0 => pE6H4 (val6H6 g)
  | 4, 1 => pE6H4 i
  | 4, 2 => pE6H4 (val6H4 e)
  | 4, 3 => pE6H5 i
  | 4, 4 => pE6H4 (val6H5 f)
  | 4, 5 => pE6H4 (val6H7 h)
  | 5, 0 => pE6H6 (val6H6 g)
  | 5, 1 => pE6H6 i
  | 5, 2 => pE6H6 (val6H4 e)
  | 5, 3 => pE6H7 i
  | 5, 4 => pE6H6 (val6H7 h)
  | 5, 5 => pE6H6 (val6H5 f)

theorem tab6H_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) :
    tab6H a b c d e f g h i = Magma.transport permE6H tr6H (dec6H a b c d e f g h i) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `16` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `98304` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6H : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6H 0 0 0 0 0 2 2 0 0
  | 1 => tab6H 0 0 0 0 0 2 2 0 2
  | 2 => tab6H 0 0 0 0 2 2 2 0 0
  | 3 => tab6H 0 0 0 0 2 2 2 0 2
  | 4 => tab6H 0 0 1 0 0 2 2 0 0
  | 5 => tab6H 0 0 1 0 0 2 2 0 2
  | 6 => tab6H 0 0 1 0 2 2 2 0 0
  | 7 => tab6H 0 0 1 0 2 2 2 0 2
  | 8 => tab6H 0 2 0 0 0 2 2 0 0
  | 9 => tab6H 0 2 0 0 0 2 2 0 2
  | 10 => tab6H 0 2 0 0 2 2 2 0 0
  | 11 => tab6H 0 2 0 0 2 2 2 0 2
  | 12 => tab6H 0 2 1 0 0 2 2 0 0
  | 13 => tab6H 0 2 1 0 0 2 2 0 2
  | 14 => tab6H 0 2 1 0 2 2 2 0 0
  | _ => tab6H 0 2 1 0 2 2 2 0 2

/-- The arguments as one mixed-radix index, which is how `rankIdx6H` is addressed. -/
def encT6H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Nat :=
  a.1 * 49152 +
    b.1 * 12288 +
    c.1 * 6144 +
    d.1 * 1536 +
    e.1 * 384 +
    f.1 * 96 +
    g.1 * 24 +
    h.1 * 6 +
    i.1

/-- Which of the `16` members a given invariant tuple is, so that `mem_of_isExact6H` can name one
rather than search the list for it. The `98288` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6H` excludes them. Read only by `native_decide`. -/
def rankIdx6H : Nat → Nat
  | 240 => 0
  | 242 => 1
  | 1008 => 2
  | 1010 => 3
  | 6384 => 4
  | 6386 => 5
  | 7152 => 6
  | 7154 => 7
  | 24816 => 8
  | 24818 => 9
  | 25584 => 10
  | 25586 => 11
  | 30960 => 12
  | 30962 => 13
  | 31728 => 14
  | 31730 => 15
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 16 :=
  ⟨min (rankIdx6H (encT6H a b c d e f g h i)) 15, by omega⟩


/-- `1` of the `70` demanded maps and `1` of the `46586` forbidden ones, enough to separate the `16`
members from the other `98288` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6H` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6H : Fin 1 → Fin 70
  | 0 => 8
def x0idx6H : Fin 1 → Fin 46586
  | 0 => 889

def endE06H (j : Fin 1) : Fin 6 → Fin 6 := endE6H (e0idx6H j)

def endX06H (j : Fin 1) : Fin 6 → Fin 6 := endX6H (x0idx6H j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6H (i : Fin 16) : Magma (Fin 6) := Magma.mk (mem6H i)

theorem end6H_isEndo (i : Fin 16) (j : Fin 70) : (end6H i).IsEndo (endE6H j) := by
  revert i j; native_decide

theorem end6H_not_isEndo (i : Fin 16) (j : Fin 46586) : ¬ (end6H i).IsEndo (endX6H j) := by
  revert i j; native_decide

/-- `rank6H` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6H` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6H a b c d e f g h i) endE06H endX06H = true) :
    mem6H (rank6H a b c d e f g h i) = tab6H a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `16` listed
members. -/
theorem mem_of_isExact6H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6H a b c d e f g h i) endE06H endX06H = true) :
    ∃ idx, mem6H idx = tab6H a b c d e f g h i :=
  ⟨_, mem_rank6H a b c d e f g h i hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6H`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6H` turns that into a member index. -/
theorem exists_end6H {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6H j))
    (hX : ∀ j, ¬ M.IsEndo (endX6H j)) : ∃ i, end6H i = M := by
  have hP : ∀ i, M.IsEndo (permE6H i) := by
    intro i; rw [permE6H_eq_endE6H]; exact hE (uidx6H i)
  have hop : M.op = Magma.transport permE6H tr6H (fun i ↦ M.op (rep6H i).1 (rep6H i).2) :=
    Magma.op_eq_transport (rep := rep6H) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H0) (a := (rep6H 0).1) (b := (rep6H 0).2)
    (val := val6H0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H1) (a := (rep6H 1).1) (b := (rep6H 1).2)
    (val := val6H1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H2) (a := (rep6H 2).1) (b := (rep6H 2).2)
    (val := val6H2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H3) (a := (rep6H 3).1) (b := (rep6H 3).2)
    (val := val6H3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H4) (a := (rep6H 4).1) (b := (rep6H 4).2)
    (val := val6H4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H5) (a := (rep6H 5).1) (b := (rep6H 5).2)
    (val := val6H5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H6) (a := (rep6H 6).1) (b := (rep6H 6).2)
    (val := val6H6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H7) (a := (rep6H 7).1) (b := (rep6H 7).2)
    (val := val6H7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6H) (idx := stabIdx6H8) (a := (rep6H 8).1) (b := (rep6H 8).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6H a b c d e f g h i = fun i ↦ M.op (rep6H i).1 (rep6H i).2 := by
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
  have key : tab6H a b c d e f g h i = M.op := by
    rw [tab6H_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6H a b c d e f g h i) endE06H endX06H = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6H j), fun j ↦ hX (x0idx6H j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6H a b c d e f g h i hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`70` monoid of `Magma.endE6H`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6H {L L' : Law.NatMagmaLaw} {i : Fin 16}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6H i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6H j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6H i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6H
    (fun k ↦ (Magma.end6H_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6H_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
