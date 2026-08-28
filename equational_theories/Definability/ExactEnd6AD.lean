import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AD` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(2 3)(4 5), (2 4)(3 5), (2 4 3 5)⟩`

`End(M)` is `141` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(2 3)`, `(2 3)(4 5)`, `(2 4)(3 5)`, `(2 4 3 5)`,
`(2 5 3 4)`, `(2 5)(3 4)`. -/
def pE6AD0 : Fin 6 → Fin 6 := id
def pE6AD1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AD2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5
def pE6AD3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6AD4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3
def pE6AD5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
def pE6AD6 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3
def pE6AD7 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2

def permE6AD : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6AD0
  | 1 => pE6AD1
  | 2 => pE6AD2
  | 3 => pE6AD3
  | 4 => pE6AD4
  | 5 => pE6AD5
  | 6 => pE6AD6
  | 7 => pE6AD7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `141` self-maps that must be endomorphisms: `000000`, `220000`, `330000`,
`440000`, `550000`, `002200`, `222200`, `332200`, `442200`, `552200`, `003300`, `223300`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AD : Fin 141 → Fin 46656
  | 0 => 0
  | 1 => 14
  | 2 => 21
  | 3 => 28
  | 4 => 35
  | 5 => 504
  | 6 => 518
  | 7 => 525
  | 8 => 532
  | 9 => 539
  | 10 => 756
  | 11 => 770
  | 12 => 777
  | 13 => 784
  | 14 => 791
  | 15 => 1008
  | 16 => 1022
  | 17 => 1029
  | 18 => 1036
  | 19 => 1043
  | 20 => 1260
  | 21 => 1274
  | 22 => 1281
  | 23 => 1288
  | 24 => 1295
  | 25 => 18144
  | 26 => 18158
  | 27 => 18165
  | 28 => 18172
  | 29 => 18179
  | 30 => 18648
  | 31 => 18662
  | 32 => 18669
  | 33 => 18676
  | 34 => 18683
  | 35 => 18900
  | 36 => 18914
  | 37 => 18921
  | 38 => 18928
  | 39 => 18935
  | 40 => 19152
  | 41 => 19166
  | 42 => 19173
  | 43 => 19180
  | 44 => 19187
  | 45 => 19404
  | 46 => 19418
  | 47 => 19425
  | 48 => 19432
  | 49 => 19439
  | 50 => 19986
  | 51 => 20166
  | 52 => 20490
  | 53 => 20670
  | 54 => 26466
  | 55 => 26646
  | 56 => 26970
  | 57 => 27150
  | 58 => 27216
  | 59 => 27230
  | 60 => 27237
  | 61 => 27244
  | 62 => 27251
  | 63 => 27720
  | 64 => 27734
  | 65 => 27741
  | 66 => 27748
  | 67 => 27755
  | 68 => 27972
  | 69 => 27986
  | 70 => 27993
  | 71 => 28000
  | 72 => 28007
  | 73 => 28224
  | 74 => 28238
  | 75 => 28245
  | 76 => 28252
  | 77 => 28259
  | 78 => 28476
  | 79 => 28490
  | 80 => 28497
  | 81 => 28504
  | 82 => 28511
  | 83 => 36288
  | 84 => 36302
  | 85 => 36309
  | 86 => 36316
  | 87 => 36323
  | 88 => 36792
  | 89 => 36806
  | 90 => 36813
  | 91 => 36820
  | 92 => 36827
  | 93 => 37044
  | 94 => 37058
  | 95 => 37065
  | 96 => 37072
  | 97 => 37079
  | 98 => 37296
  | 99 => 37310
  | 100 => 37317
  | 101 => 37324
  | 102 => 37331
  | 103 => 37548
  | 104 => 37562
  | 105 => 37569
  | 106 => 37576
  | 107 => 37583
  | 108 => 38130
  | 109 => 38310
  | 110 => 38634
  | 111 => 38814
  | 112 => 44610
  | 113 => 44790
  | 114 => 45114
  | 115 => 45294
  | 116 => 45360
  | 117 => 45374
  | 118 => 45381
  | 119 => 45388
  | 120 => 45395
  | 121 => 45864
  | 122 => 45878
  | 123 => 45885
  | 124 => 45892
  | 125 => 45899
  | 126 => 46116
  | 127 => 46130
  | 128 => 46137
  | 129 => 46144
  | 130 => 46151
  | 131 => 46368
  | 132 => 46382
  | 133 => 46389
  | 134 => 46396
  | 135 => 46403
  | 136 => 46620
  | 137 => 46634
  | 138 => 46641
  | 139 => 46648
  | _ => 46655

def endE6AD (j : Fin 141) : Fin 6 → Fin 6 := allMaps6 (eidx6AD j)

/-- Indices of the other `46515`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AD : Array Nat := #[
  0, 14, 21, 28, 35, 504, 518, 525, 532, 539, 756, 770, 777, 784, 791, 1008, 1022, 1029, 1036,
  1043, 1260, 1274, 1281, 1288, 1295, 18144, 18158, 18165, 18172, 18179, 18648, 18662, 18669,
  18676, 18683, 18900, 18914, 18921, 18928, 18935, 19152, 19166, 19173, 19180, 19187, 19404,
  19418, 19425, 19432, 19439, 19986, 20166, 20490, 20670, 26466, 26646, 26970, 27150, 27216,
  27230, 27237, 27244, 27251, 27720, 27734, 27741, 27748, 27755, 27972, 27986, 27993, 28000,
  28007, 28224, 28238, 28245, 28252, 28259, 28476, 28490, 28497, 28504, 28511, 36288, 36302,
  36309, 36316, 36323, 36792, 36806, 36813, 36820, 36827, 37044, 37058, 37065, 37072, 37079,
  37296, 37310, 37317, 37324, 37331, 37548, 37562, 37569, 37576, 37583, 38130, 38310, 38634,
  38814, 44610, 44790, 45114, 45294, 45360, 45374, 45381, 45388, 45395, 45864, 45878, 45885,
  45892, 45899, 46116, 46130, 46137, 46144, 46151, 46368, 46382, 46389, 46396, 46403, 46620,
  46634, 46641, 46648, 46655]

def xarr6AD : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AD.contains i)

def xidx6AD (j : Fin 46515) : Fin 46656 :=
  ⟨min (xarr6AD.getD j.1 0) 46655, by omega⟩

def endX6AD (j : Fin 46515) : Fin 6 → Fin 6 := allMaps6 (xidx6AD j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AD` is given. -/
def uidx6AD : Fin 8 → Fin 141
  | 0 => 113
  | 1 => 109
  | 2 => 112
  | 3 => 108
  | 4 => 57
  | 5 => 53
  | 6 => 56
  | 7 => 52

theorem permE6AD_eq_endE6AD (i : Fin 8) : permE6AD i = endE6AD (uidx6AD i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6AD : Fin 11 → Fin 6 × Fin 6
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
def tr6AD : Fin 6 → Fin 6 → Fin 11 × Fin 8
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
def stabIdx6AD0 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6AD0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AD1 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6AD1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AD2 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AD2 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `8` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AD3 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6AD3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AD4 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6AD4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AD5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AD5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AD6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AD6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AD7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AD7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AD8 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AD8 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AD9 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AD9 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `10`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AD10 : Fin 1 → Fin 8
  | 0 => 0

/-- The `11` orbit values named by the family's arguments. -/
def dec6AD (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 11 → Fin 6
  | 0 => val6AD0 a
  | 1 => val6AD1 b
  | 2 => val6AD2 c
  | 3 => val6AD3 d
  | 4 => val6AD4 e
  | 5 => val6AD5 f
  | 6 => val6AD6 g
  | 7 => val6AD7 h
  | 8 => val6AD8 i
  | 9 => val6AD9 j
  | 10 => k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AD_eq_transport`). -/
def tab6AD (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AD0 a
  | 0, 1 => val6AD1 b
  | 0, 2 => val6AD2 c
  | 0, 3 => pE6AD2 (val6AD2 c)
  | 0, 4 => pE6AD4 (val6AD2 c)
  | 0, 5 => pE6AD6 (val6AD2 c)
  | 1, 0 => val6AD3 d
  | 1, 1 => val6AD4 e
  | 1, 2 => val6AD5 f
  | 1, 3 => pE6AD2 (val6AD5 f)
  | 1, 4 => pE6AD4 (val6AD5 f)
  | 1, 5 => pE6AD6 (val6AD5 f)
  | 2, 0 => val6AD6 g
  | 2, 1 => val6AD7 h
  | 2, 2 => val6AD8 i
  | 2, 3 => val6AD9 j
  | 2, 4 => k
  | 2, 5 => pE6AD1 k
  | 3, 0 => pE6AD2 (val6AD6 g)
  | 3, 1 => pE6AD2 (val6AD7 h)
  | 3, 2 => pE6AD2 (val6AD9 j)
  | 3, 3 => pE6AD2 (val6AD8 i)
  | 3, 4 => pE6AD2 k
  | 3, 5 => pE6AD3 k
  | 4, 0 => pE6AD4 (val6AD6 g)
  | 4, 1 => pE6AD4 (val6AD7 h)
  | 4, 2 => pE6AD4 k
  | 4, 3 => pE6AD5 k
  | 4, 4 => pE6AD4 (val6AD8 i)
  | 4, 5 => pE6AD4 (val6AD9 j)
  | 5, 0 => pE6AD6 (val6AD6 g)
  | 5, 1 => pE6AD6 (val6AD7 h)
  | 5, 2 => pE6AD6 k
  | 5, 3 => pE6AD7 k
  | 5, 4 => pE6AD6 (val6AD9 j)
  | 5, 5 => pE6AD6 (val6AD8 i)

theorem tab6AD_eq_transport (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    :
    tab6AD a b c d e f g h i j k = Magma.transport permE6AD tr6AD (dec6AD a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `12` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `393216` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6AD : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AD 0 0 0 0 0 1 2 3 2 2 2
  | 1 => tab6AD 0 0 0 1 0 0 2 3 2 2 2
  | 2 => tab6AD 0 0 2 0 0 3 0 1 2 3 4
  | 3 => tab6AD 0 0 2 1 0 3 0 0 2 3 4
  | 4 => tab6AD 0 0 2 1 0 3 0 1 2 3 4
  | 5 => tab6AD 0 1 0 0 0 0 2 3 2 2 2
  | 6 => tab6AD 0 1 0 0 0 1 2 3 2 2 2
  | 7 => tab6AD 0 1 0 1 0 0 2 3 2 2 2
  | 8 => tab6AD 0 1 0 1 0 1 2 3 2 2 2
  | 9 => tab6AD 0 1 2 0 0 3 0 0 2 3 4
  | 10 => tab6AD 0 1 2 1 0 3 0 0 2 3 4
  | 11 => tab6AD 0 1 2 1 0 3 0 1 2 3 4

/-- The arguments as one mixed-radix index, which is how `rankIdx6AD` is addressed. -/
def encT6AD (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Nat :=
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

/-- Which of the `12` members a given invariant tuple is, so that `mem_of_isExact6AD` can name one
rather than search the list for it. The `393204` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6AD` excludes them. Read only by `native_decide`. -/
def rankIdx6AD : Nat → Nat
  | 2654 => 0
  | 13406 => 1
  | 53926 => 2
  | 66118 => 3
  | 66214 => 4
  | 99422 => 5
  | 100958 => 6
  | 111710 => 7
  | 113246 => 8
  | 152134 => 9
  | 164422 => 10
  | 164518 => 11
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AD (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 12 :=
  ⟨min (rankIdx6AD (encT6AD a b c d e f g h i j k)) 11, by omega⟩


/-- `2` of the `141` demanded maps and `3` of the `46515` forbidden ones, enough to separate the
`12` members from the other `393204` invariant tuples between them. The certificate still demands
and forbids all `46656`; these are the lists `mem_rank6AD` scans, once per tuple, with a scan that
is quadratic in their length. -/
def e0idx6AD : Fin 2 → Fin 141
  | 0 => 7
  | 1 => 8
def x0idx6AD : Fin 3 → Fin 46515
  | 0 => 5
  | 1 => 67
  | 2 => 9306

def endE06AD (j : Fin 2) : Fin 6 → Fin 6 := endE6AD (e0idx6AD j)

def endX06AD (j : Fin 3) : Fin 6 → Fin 6 := endX6AD (x0idx6AD j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AD (i : Fin 12) : Magma (Fin 6) := Magma.mk (mem6AD i)

theorem end6AD_isEndo (i : Fin 12) (j : Fin 141) : (end6AD i).IsEndo (endE6AD j) := by
  revert i j; native_decide

theorem end6AD_not_isEndo (i : Fin 12) (j : Fin 46515) : ¬ (end6AD i).IsEndo (endX6AD j) := by
  revert i j; native_decide

/-- `rank6AD` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AD` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AD (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6AD a b c d e f g h i j k) endE06AD endX06AD = true) :
    mem6AD (rank6AD a b c d e f g h i j k) = tab6AD a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `12` listed
members. -/
theorem mem_of_isExact6AD (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6AD a b c d e f g h i j k) endE06AD endX06AD = true) :
    ∃ idx, mem6AD idx = tab6AD a b c d e f g h i j k :=
  ⟨_, mem_rank6AD a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AD`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AD` turns that into a member index. -/
theorem exists_end6AD {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AD j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AD j)) : ∃ i, end6AD i = M := by
  have hP : ∀ i, M.IsEndo (permE6AD i) := by
    intro i; rw [permE6AD_eq_endE6AD]; exact hE (uidx6AD i)
  have hop : M.op = Magma.transport permE6AD tr6AD (fun i ↦ M.op (rep6AD i).1 (rep6AD i).2) :=
    Magma.op_eq_transport (rep := rep6AD) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD0) (a := (rep6AD 0).1) (b := (rep6AD 0).2)
    (val := val6AD0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD1) (a := (rep6AD 1).1) (b := (rep6AD 1).2)
    (val := val6AD1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD2) (a := (rep6AD 2).1) (b := (rep6AD 2).2)
    (val := val6AD2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD3) (a := (rep6AD 3).1) (b := (rep6AD 3).2)
    (val := val6AD3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD4) (a := (rep6AD 4).1) (b := (rep6AD 4).2)
    (val := val6AD4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD5) (a := (rep6AD 5).1) (b := (rep6AD 5).2)
    (val := val6AD5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD6) (a := (rep6AD 6).1) (b := (rep6AD 6).2)
    (val := val6AD6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD7) (a := (rep6AD 7).1) (b := (rep6AD 7).2)
    (val := val6AD7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD8) (a := (rep6AD 8).1) (b := (rep6AD 8).2)
    (val := val6AD8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD9) (a := (rep6AD 9).1) (b := (rep6AD 9).2)
    (val := val6AD9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6AD) (idx := stabIdx6AD10) (a := (rep6AD 10).1) (b := (rep6AD 10).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6AD a b c d e f g h i j k = fun i ↦ M.op (rep6AD i).1 (rep6AD i).2 := by
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
  have key : tab6AD a b c d e f g h i j k = M.op := by
    rw [tab6AD_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AD a b c d e f g h i j k) endE06AD endX06AD = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AD j), fun j ↦ hX (x0idx6AD j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AD a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`141` monoid of `Magma.endE6AD`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AD {L L' : Law.NatMagmaLaw} {i : Fin 12}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AD i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AD j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AD i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AD
    (fun k ↦ (Magma.end6AD_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AD_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
