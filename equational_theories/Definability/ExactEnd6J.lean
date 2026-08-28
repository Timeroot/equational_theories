import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `J` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(2 3)(4 5), (2 4)(3 5), (2 4 3 5)⟩`

`End(M)` is `150` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(2 3)`, `(2 3)(4 5)`, `(2 4)(3 5)`, `(2 4 3 5)`,
`(2 5 3 4)`, `(2 5)(3 4)`. -/
def pE6J0 : Fin 6 → Fin 6 := id
def pE6J1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6J2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5
def pE6J3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6J4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3
def pE6J5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
def pE6J6 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3
def pE6J7 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2

def permE6J : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6J0
  | 1 => pE6J1
  | 2 => pE6J2
  | 3 => pE6J3
  | 4 => pE6J4
  | 5 => pE6J5
  | 6 => pE6J6
  | 7 => pE6J7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `150` self-maps that must be endomorphisms: `000000`, `010000`, `220000`,
`330000`, `440000`, `550000`, `002200`, `222200`, `332200`, `442200`, `552200`, `013200`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6J : Fin 150 → Fin 46656
  | 0 => 0
  | 1 => 6
  | 2 => 14
  | 3 => 21
  | 4 => 28
  | 5 => 35
  | 6 => 504
  | 7 => 518
  | 8 => 525
  | 9 => 532
  | 10 => 539
  | 11 => 546
  | 12 => 726
  | 13 => 756
  | 14 => 770
  | 15 => 777
  | 16 => 784
  | 17 => 791
  | 18 => 1008
  | 19 => 1022
  | 20 => 1029
  | 21 => 1036
  | 22 => 1043
  | 23 => 1050
  | 24 => 1230
  | 25 => 1260
  | 26 => 1274
  | 27 => 1281
  | 28 => 1288
  | 29 => 1295
  | 30 => 18144
  | 31 => 18158
  | 32 => 18165
  | 33 => 18172
  | 34 => 18179
  | 35 => 18648
  | 36 => 18662
  | 37 => 18669
  | 38 => 18676
  | 39 => 18683
  | 40 => 18900
  | 41 => 18914
  | 42 => 18921
  | 43 => 18928
  | 44 => 18935
  | 45 => 19152
  | 46 => 19166
  | 47 => 19173
  | 48 => 19180
  | 49 => 19187
  | 50 => 19404
  | 51 => 19418
  | 52 => 19425
  | 53 => 19432
  | 54 => 19439
  | 55 => 19446
  | 56 => 19986
  | 57 => 20166
  | 58 => 20490
  | 59 => 20670
  | 60 => 25926
  | 61 => 26466
  | 62 => 26646
  | 63 => 26970
  | 64 => 27150
  | 65 => 27216
  | 66 => 27230
  | 67 => 27237
  | 68 => 27244
  | 69 => 27251
  | 70 => 27720
  | 71 => 27734
  | 72 => 27741
  | 73 => 27748
  | 74 => 27755
  | 75 => 27972
  | 76 => 27986
  | 77 => 27993
  | 78 => 28000
  | 79 => 28007
  | 80 => 28224
  | 81 => 28238
  | 82 => 28245
  | 83 => 28252
  | 84 => 28259
  | 85 => 28476
  | 86 => 28490
  | 87 => 28497
  | 88 => 28504
  | 89 => 28511
  | 90 => 36288
  | 91 => 36302
  | 92 => 36309
  | 93 => 36316
  | 94 => 36323
  | 95 => 36792
  | 96 => 36806
  | 97 => 36813
  | 98 => 36820
  | 99 => 36827
  | 100 => 37044
  | 101 => 37058
  | 102 => 37065
  | 103 => 37072
  | 104 => 37079
  | 105 => 37296
  | 106 => 37310
  | 107 => 37317
  | 108 => 37324
  | 109 => 37331
  | 110 => 37548
  | 111 => 37562
  | 112 => 37569
  | 113 => 37576
  | 114 => 37583
  | 115 => 37590
  | 116 => 38130
  | 117 => 38310
  | 118 => 38634
  | 119 => 38814
  | 120 => 44070
  | 121 => 44610
  | 122 => 44790
  | 123 => 45114
  | 124 => 45294
  | 125 => 45360
  | 126 => 45374
  | 127 => 45381
  | 128 => 45388
  | 129 => 45395
  | 130 => 45864
  | 131 => 45878
  | 132 => 45885
  | 133 => 45892
  | 134 => 45899
  | 135 => 46116
  | 136 => 46130
  | 137 => 46137
  | 138 => 46144
  | 139 => 46151
  | 140 => 46368
  | 141 => 46382
  | 142 => 46389
  | 143 => 46396
  | 144 => 46403
  | 145 => 46620
  | 146 => 46634
  | 147 => 46641
  | 148 => 46648
  | _ => 46655

def endE6J (j : Fin 150) : Fin 6 → Fin 6 := allMaps6 (eidx6J j)

/-- Indices of the other `46506`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6J : Array Nat := #[
  0, 6, 14, 21, 28, 35, 504, 518, 525, 532, 539, 546, 726, 756, 770, 777, 784, 791, 1008, 1022,
  1029, 1036, 1043, 1050, 1230, 1260, 1274, 1281, 1288, 1295, 18144, 18158, 18165, 18172, 18179,
  18648, 18662, 18669, 18676, 18683, 18900, 18914, 18921, 18928, 18935, 19152, 19166, 19173,
  19180, 19187, 19404, 19418, 19425, 19432, 19439, 19446, 19986, 20166, 20490, 20670, 25926,
  26466, 26646, 26970, 27150, 27216, 27230, 27237, 27244, 27251, 27720, 27734, 27741, 27748,
  27755, 27972, 27986, 27993, 28000, 28007, 28224, 28238, 28245, 28252, 28259, 28476, 28490,
  28497, 28504, 28511, 36288, 36302, 36309, 36316, 36323, 36792, 36806, 36813, 36820, 36827,
  37044, 37058, 37065, 37072, 37079, 37296, 37310, 37317, 37324, 37331, 37548, 37562, 37569,
  37576, 37583, 37590, 38130, 38310, 38634, 38814, 44070, 44610, 44790, 45114, 45294, 45360,
  45374, 45381, 45388, 45395, 45864, 45878, 45885, 45892, 45899, 46116, 46130, 46137, 46144,
  46151, 46368, 46382, 46389, 46396, 46403, 46620, 46634, 46641, 46648, 46655]

def xarr6J : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6J.contains i)

def xidx6J (j : Fin 46506) : Fin 46656 :=
  ⟨min (xarr6J.getD j.1 0) 46655, by omega⟩

def endX6J (j : Fin 46506) : Fin 6 → Fin 6 := allMaps6 (xidx6J j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6J` is given. -/
def uidx6J : Fin 8 → Fin 150
  | 0 => 122
  | 1 => 117
  | 2 => 121
  | 3 => 116
  | 4 => 64
  | 5 => 59
  | 6 => 63
  | 7 => 58

theorem permE6J_eq_endE6J (i : Fin 8) : permE6J i = endE6J (uidx6J i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6J : Fin 11 → Fin 6 × Fin 6
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
def tr6J : Fin 6 → Fin 6 → Fin 11 × Fin 8
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
def stabIdx6J0 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6J0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6J1 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6J1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6J2 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6J2 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `8` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6J3 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6J3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6J4 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6J4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6J5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6J5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6J6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6J6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6J7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6J7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6J8 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6J8 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6J9 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6J9 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `10`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6J10 : Fin 1 → Fin 8
  | 0 => 0

/-- The `11` orbit values named by the family's arguments. -/
def dec6J (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 11 → Fin 6
  | 0 => val6J0 a
  | 1 => val6J1 b
  | 2 => val6J2 c
  | 3 => val6J3 d
  | 4 => val6J4 e
  | 5 => val6J5 f
  | 6 => val6J6 g
  | 7 => val6J7 h
  | 8 => val6J8 i
  | 9 => val6J9 j
  | 10 => k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6J_eq_transport`). -/
def tab6J (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6J0 a
  | 0, 1 => val6J1 b
  | 0, 2 => val6J2 c
  | 0, 3 => pE6J2 (val6J2 c)
  | 0, 4 => pE6J4 (val6J2 c)
  | 0, 5 => pE6J6 (val6J2 c)
  | 1, 0 => val6J3 d
  | 1, 1 => val6J4 e
  | 1, 2 => val6J5 f
  | 1, 3 => pE6J2 (val6J5 f)
  | 1, 4 => pE6J4 (val6J5 f)
  | 1, 5 => pE6J6 (val6J5 f)
  | 2, 0 => val6J6 g
  | 2, 1 => val6J7 h
  | 2, 2 => val6J8 i
  | 2, 3 => val6J9 j
  | 2, 4 => k
  | 2, 5 => pE6J1 k
  | 3, 0 => pE6J2 (val6J6 g)
  | 3, 1 => pE6J2 (val6J7 h)
  | 3, 2 => pE6J2 (val6J9 j)
  | 3, 3 => pE6J2 (val6J8 i)
  | 3, 4 => pE6J2 k
  | 3, 5 => pE6J3 k
  | 4, 0 => pE6J4 (val6J6 g)
  | 4, 1 => pE6J4 (val6J7 h)
  | 4, 2 => pE6J4 k
  | 4, 3 => pE6J5 k
  | 4, 4 => pE6J4 (val6J8 i)
  | 4, 5 => pE6J4 (val6J9 j)
  | 5, 0 => pE6J6 (val6J6 g)
  | 5, 1 => pE6J6 (val6J7 h)
  | 5, 2 => pE6J6 k
  | 5, 3 => pE6J7 k
  | 5, 4 => pE6J6 (val6J9 j)
  | 5, 5 => pE6J6 (val6J8 i)

theorem tab6J_eq_transport (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) :
    tab6J a b c d e f g h i j k = Magma.transport permE6J tr6J (dec6J a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `393216` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6J : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6J 0 0 0 0 0 0 2 3 2 2 2
  | 1 => tab6J 0 0 0 1 0 1 2 3 2 2 2
  | 2 => tab6J 0 0 2 0 0 3 0 0 2 3 4
  | 3 => tab6J 0 1 2 0 0 3 0 1 2 3 4

/-- The arguments as one mixed-radix index, which is how `rankIdx6J` is addressed. -/
def encT6J (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Nat :=
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

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6J` can name one
rather than search the list for it. The `393212` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6J` excludes them. Read only by `native_decide`. -/
def rankIdx6J : Nat → Nat
  | 1118 => 0
  | 14942 => 1
  | 53830 => 2
  | 152230 => 3
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6J (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 4 :=
  ⟨min (rankIdx6J (encT6J a b c d e f g h i j k)) 3, by omega⟩


/-- `2` of the `150` demanded maps and `2` of the `46506` forbidden ones, enough to separate the `4`
members from the other `393212` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6J` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6J : Fin 2 → Fin 150
  | 0 => 8
  | 1 => 11
def x0idx6J : Fin 2 → Fin 46506
  | 0 => 66
  | 1 => 9301

def endE06J (j : Fin 2) : Fin 6 → Fin 6 := endE6J (e0idx6J j)

def endX06J (j : Fin 2) : Fin 6 → Fin 6 := endX6J (x0idx6J j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6J (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6J i)

theorem end6J_isEndo (i : Fin 4) (j : Fin 150) : (end6J i).IsEndo (endE6J j) := by
  revert i j; native_decide

theorem end6J_not_isEndo (i : Fin 4) (j : Fin 46506) : ¬ (end6J i).IsEndo (endX6J j) := by
  revert i j; native_decide

/-- `rank6J` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6J` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6J (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6J a b c d e f g h i j k) endE06J endX06J = true) :
    mem6J (rank6J a b c d e f g h i j k) = tab6J a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6J (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6J a b c d e f g h i j k) endE06J endX06J = true) :
    ∃ idx, mem6J idx = tab6J a b c d e f g h i j k :=
  ⟨_, mem_rank6J a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6J`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6J` turns that into a member index. -/
theorem exists_end6J {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6J j))
    (hX : ∀ j, ¬ M.IsEndo (endX6J j)) : ∃ i, end6J i = M := by
  have hP : ∀ i, M.IsEndo (permE6J i) := by
    intro i; rw [permE6J_eq_endE6J]; exact hE (uidx6J i)
  have hop : M.op = Magma.transport permE6J tr6J (fun i ↦ M.op (rep6J i).1 (rep6J i).2) :=
    Magma.op_eq_transport (rep := rep6J) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J0) (a := (rep6J 0).1) (b := (rep6J 0).2)
    (val := val6J0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J1) (a := (rep6J 1).1) (b := (rep6J 1).2)
    (val := val6J1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J2) (a := (rep6J 2).1) (b := (rep6J 2).2)
    (val := val6J2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J3) (a := (rep6J 3).1) (b := (rep6J 3).2)
    (val := val6J3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J4) (a := (rep6J 4).1) (b := (rep6J 4).2)
    (val := val6J4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J5) (a := (rep6J 5).1) (b := (rep6J 5).2)
    (val := val6J5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J6) (a := (rep6J 6).1) (b := (rep6J 6).2)
    (val := val6J6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J7) (a := (rep6J 7).1) (b := (rep6J 7).2)
    (val := val6J7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J8) (a := (rep6J 8).1) (b := (rep6J 8).2)
    (val := val6J8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J9) (a := (rep6J 9).1) (b := (rep6J 9).2)
    (val := val6J9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6J) (idx := stabIdx6J10) (a := (rep6J 10).1) (b := (rep6J 10).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6J a b c d e f g h i j k = fun i ↦ M.op (rep6J i).1 (rep6J i).2 := by
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
  have key : tab6J a b c d e f g h i j k = M.op := by
    rw [tab6J_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6J a b c d e f g h i j k) endE06J endX06J = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6J j), fun j ↦ hX (x0idx6J j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6J a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`150` monoid of `Magma.endE6J`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6J {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6J i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6J j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6J i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6J
    (fun k ↦ (Magma.end6J_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6J_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
