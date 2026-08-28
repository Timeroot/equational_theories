import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `M` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `141` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6M0 : Fin 6 → Fin 6 := id
def pE6M1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6M2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6M3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6M4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6M5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6M6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6M7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6M8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6M9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6M10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6M11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6M : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6M0
  | 1 => pE6M1
  | 2 => pE6M2
  | 3 => pE6M3
  | 4 => pE6M4
  | 5 => pE6M5
  | 6 => pE6M6
  | 7 => pE6M7
  | 8 => pE6M8
  | 9 => pE6M9
  | 10 => pE6M10
  | 11 => pE6M11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `141` self-maps that must be endomorphisms: `102222`, `012222`, `222222`,
`332222`, `442222`, `552222`, `102322`, `012322`, `222322`, `442322`, `552322`, `102422`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6M : Fin 141 → Fin 46656
  | 0 => 18649
  | 1 => 18654
  | 2 => 18662
  | 3 => 18669
  | 4 => 18676
  | 5 => 18683
  | 6 => 18865
  | 7 => 18870
  | 8 => 18878
  | 9 => 18892
  | 10 => 18899
  | 11 => 19081
  | 12 => 19086
  | 13 => 19094
  | 14 => 19101
  | 15 => 19115
  | 16 => 19297
  | 17 => 19302
  | 18 => 19310
  | 19 => 19317
  | 20 => 19324
  | 21 => 19945
  | 22 => 19950
  | 23 => 19958
  | 24 => 19972
  | 25 => 19979
  | 26 => 20377
  | 27 => 20382
  | 28 => 20390
  | 29 => 20411
  | 30 => 20593
  | 31 => 20598
  | 32 => 20606
  | 33 => 20620
  | 34 => 21241
  | 35 => 21246
  | 36 => 21254
  | 37 => 21261
  | 38 => 21275
  | 39 => 21457
  | 40 => 21462
  | 41 => 21470
  | 42 => 21491
  | 43 => 21889
  | 44 => 21894
  | 45 => 21902
  | 46 => 21909
  | 47 => 22537
  | 48 => 22542
  | 49 => 22550
  | 50 => 22557
  | 51 => 22564
  | 52 => 22753
  | 53 => 22758
  | 54 => 22766
  | 55 => 22780
  | 56 => 22969
  | 57 => 22974
  | 58 => 22982
  | 59 => 22989
  | 60 => 26425
  | 61 => 26430
  | 62 => 26438
  | 63 => 26452
  | 64 => 26459
  | 65 => 26857
  | 66 => 26862
  | 67 => 26870
  | 68 => 26891
  | 69 => 27073
  | 70 => 27078
  | 71 => 27086
  | 72 => 27100
  | 73 => 29017
  | 74 => 29022
  | 75 => 29030
  | 76 => 29051
  | 77 => 29665
  | 78 => 29670
  | 79 => 29678
  | 80 => 30313
  | 81 => 30318
  | 82 => 30326
  | 83 => 30340
  | 84 => 30745
  | 85 => 30750
  | 86 => 30758
  | 87 => 34201
  | 88 => 34206
  | 89 => 34214
  | 90 => 34221
  | 91 => 34235
  | 92 => 34417
  | 93 => 34422
  | 94 => 34430
  | 95 => 34451
  | 96 => 34849
  | 97 => 34854
  | 98 => 34862
  | 99 => 34869
  | 100 => 35497
  | 101 => 35502
  | 102 => 35510
  | 103 => 35531
  | 104 => 36145
  | 105 => 36150
  | 106 => 36158
  | 107 => 38089
  | 108 => 38094
  | 109 => 38102
  | 110 => 38109
  | 111 => 38305
  | 112 => 38310
  | 113 => 38318
  | 114 => 41977
  | 115 => 41982
  | 116 => 41990
  | 117 => 41997
  | 118 => 42004
  | 119 => 42193
  | 120 => 42198
  | 121 => 42206
  | 122 => 42220
  | 123 => 42409
  | 124 => 42414
  | 125 => 42422
  | 126 => 42429
  | 127 => 43273
  | 128 => 43278
  | 129 => 43286
  | 130 => 43300
  | 131 => 43705
  | 132 => 43710
  | 133 => 43718
  | 134 => 44569
  | 135 => 44574
  | 136 => 44582
  | 137 => 44589
  | 138 => 44785
  | 139 => 44790
  | _ => 44798

def endE6M (j : Fin 141) : Fin 6 → Fin 6 := allMaps6 (eidx6M j)

/-- Indices of the other `46515`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6M : Array Nat := #[
  18649, 18654, 18662, 18669, 18676, 18683, 18865, 18870, 18878, 18892, 18899, 19081, 19086,
  19094, 19101, 19115, 19297, 19302, 19310, 19317, 19324, 19945, 19950, 19958, 19972, 19979,
  20377, 20382, 20390, 20411, 20593, 20598, 20606, 20620, 21241, 21246, 21254, 21261, 21275,
  21457, 21462, 21470, 21491, 21889, 21894, 21902, 21909, 22537, 22542, 22550, 22557, 22564,
  22753, 22758, 22766, 22780, 22969, 22974, 22982, 22989, 26425, 26430, 26438, 26452, 26459,
  26857, 26862, 26870, 26891, 27073, 27078, 27086, 27100, 29017, 29022, 29030, 29051, 29665,
  29670, 29678, 30313, 30318, 30326, 30340, 30745, 30750, 30758, 34201, 34206, 34214, 34221,
  34235, 34417, 34422, 34430, 34451, 34849, 34854, 34862, 34869, 35497, 35502, 35510, 35531,
  36145, 36150, 36158, 38089, 38094, 38102, 38109, 38305, 38310, 38318, 41977, 41982, 41990,
  41997, 42004, 42193, 42198, 42206, 42220, 42409, 42414, 42422, 42429, 43273, 43278, 43286,
  43300, 43705, 43710, 43718, 44569, 44574, 44582, 44589, 44785, 44790, 44798]

def xarr6M : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6M.contains i)

def xidx6M (j : Fin 46515) : Fin 46656 :=
  ⟨min (xarr6M.getD j.1 0) 46655, by omega⟩

def endX6M (j : Fin 46515) : Fin 6 → Fin 6 := allMaps6 (xidx6M j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6M` is given. -/
def uidx6M : Fin 12 → Fin 141
  | 0 => 139
  | 1 => 112
  | 2 => 132
  | 3 => 85
  | 4 => 105
  | 5 => 78
  | 6 => 138
  | 7 => 111
  | 8 => 131
  | 9 => 84
  | 10 => 104
  | 11 => 77

theorem permE6M_eq_endE6M (i : Fin 12) : permE6M i = endE6M (uidx6M i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6M : Fin 11 → Fin 6 × Fin 6
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
def tr6M : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6M0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6M0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6M1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6M1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6M2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6M2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6M3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6M3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6M4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6M4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6M5 : Fin 12 → Fin 12
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
def val6M5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6M6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6M6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6M7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6M7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6M8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6M8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6M9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6M9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6M10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6M10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6M (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6M0 a
  | 1 => val6M1 b
  | 2 => val6M2 c
  | 3 => val6M3 d
  | 4 => val6M4 e
  | 5 => val6M5 f
  | 6 => val6M6 g
  | 7 => val6M7 h
  | 8 => val6M8 i
  | 9 => val6M9 j
  | 10 => val6M10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6M_eq_transport`). -/
def tab6M (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6M0 a
  | 0, 1 => val6M1 b
  | 0, 2 => val6M2 c
  | 0, 3 => val6M3 d
  | 0, 4 => pE6M2 (val6M3 d)
  | 0, 5 => pE6M4 (val6M3 d)
  | 1, 0 => pE6M6 (val6M1 b)
  | 1, 1 => pE6M6 (val6M0 a)
  | 1, 2 => pE6M6 (val6M2 c)
  | 1, 3 => pE6M6 (val6M3 d)
  | 1, 4 => pE6M8 (val6M3 d)
  | 1, 5 => pE6M10 (val6M3 d)
  | 2, 0 => val6M4 e
  | 2, 1 => pE6M6 (val6M4 e)
  | 2, 2 => val6M5 f
  | 2, 3 => val6M6 g
  | 2, 4 => pE6M2 (val6M6 g)
  | 2, 5 => pE6M4 (val6M6 g)
  | 3, 0 => val6M7 h
  | 3, 1 => pE6M6 (val6M7 h)
  | 3, 2 => val6M8 i
  | 3, 3 => val6M9 j
  | 3, 4 => val6M10 k
  | 3, 5 => pE6M1 (val6M10 k)
  | 4, 0 => pE6M2 (val6M7 h)
  | 4, 1 => pE6M8 (val6M7 h)
  | 4, 2 => pE6M2 (val6M8 i)
  | 4, 3 => pE6M2 (val6M10 k)
  | 4, 4 => pE6M2 (val6M9 j)
  | 4, 5 => pE6M3 (val6M10 k)
  | 5, 0 => pE6M4 (val6M7 h)
  | 5, 1 => pE6M10 (val6M7 h)
  | 5, 2 => pE6M4 (val6M8 i)
  | 5, 3 => pE6M4 (val6M10 k)
  | 5, 4 => pE6M5 (val6M10 k)
  | 5, 5 => pE6M4 (val6M9 j)

theorem tab6M_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6M a b c d e f g h i j k = Magma.transport permE6M tr6M (dec6M a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6M : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6M 2 2 1 1 2 0 0 3 1 0 1
  | 1 => tab6M 2 2 2 3 1 0 1 1 0 0 2

/-- The arguments as one mixed-radix index, which is how `rankIdx6M` is addressed. -/
def encT6M (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
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

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6M` can name one
rather than search the list for it. The `41470` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6M` excludes them. Read only by `native_decide`. -/
def rankIdx6M : Nat → Nat
  | 39097 => 0
  | 41298 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6M (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 2 :=
  ⟨min (rankIdx6M (encT6M a b c d e f g h i j k)) 1, by omega⟩


/-- `2` of the `141` demanded maps and `2` of the `46515` forbidden ones, enough to separate the `2`
members from the other `41470` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6M` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6M : Fin 2 → Fin 141
  | 0 => 0
  | 1 => 9
def x0idx6M : Fin 2 → Fin 46515
  | 0 => 3110
  | 1 => 27920

def endE06M (j : Fin 2) : Fin 6 → Fin 6 := endE6M (e0idx6M j)

def endX06M (j : Fin 2) : Fin 6 → Fin 6 := endX6M (x0idx6M j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6M (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6M i)

theorem end6M_isEndo (i : Fin 2) (j : Fin 141) : (end6M i).IsEndo (endE6M j) := by
  revert i j; native_decide

theorem end6M_not_isEndo (i : Fin 2) (j : Fin 46515) : ¬ (end6M i).IsEndo (endX6M j) := by
  revert i j; native_decide

/-- `rank6M` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6M` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6M (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6M a b c d e f g h i j k) endE06M endX06M = true) :
    mem6M (rank6M a b c d e f g h i j k) = tab6M a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6M (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6M a b c d e f g h i j k) endE06M endX06M = true) :
    ∃ idx, mem6M idx = tab6M a b c d e f g h i j k :=
  ⟨_, mem_rank6M a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6M`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6M` turns that into a member index. -/
theorem exists_end6M {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6M j))
    (hX : ∀ j, ¬ M.IsEndo (endX6M j)) : ∃ i, end6M i = M := by
  have hP : ∀ i, M.IsEndo (permE6M i) := by
    intro i; rw [permE6M_eq_endE6M]; exact hE (uidx6M i)
  have hop : M.op = Magma.transport permE6M tr6M (fun i ↦ M.op (rep6M i).1 (rep6M i).2) :=
    Magma.op_eq_transport (rep := rep6M) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M0) (a := (rep6M 0).1) (b := (rep6M 0).2)
    (val := val6M0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M1) (a := (rep6M 1).1) (b := (rep6M 1).2)
    (val := val6M1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M2) (a := (rep6M 2).1) (b := (rep6M 2).2)
    (val := val6M2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M3) (a := (rep6M 3).1) (b := (rep6M 3).2)
    (val := val6M3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M4) (a := (rep6M 4).1) (b := (rep6M 4).2)
    (val := val6M4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M5) (a := (rep6M 5).1) (b := (rep6M 5).2)
    (val := val6M5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M6) (a := (rep6M 6).1) (b := (rep6M 6).2)
    (val := val6M6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M7) (a := (rep6M 7).1) (b := (rep6M 7).2)
    (val := val6M7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M8) (a := (rep6M 8).1) (b := (rep6M 8).2)
    (val := val6M8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M9) (a := (rep6M 9).1) (b := (rep6M 9).2)
    (val := val6M9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6M) (idx := stabIdx6M10) (a := (rep6M 10).1) (b := (rep6M 10).2)
    (val := val6M10) hP (by decide) (by decide)
  have hdec : dec6M a b c d e f g h i j k = fun i ↦ M.op (rep6M i).1 (rep6M i).2 := by
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
  have key : tab6M a b c d e f g h i j k = M.op := by
    rw [tab6M_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6M a b c d e f g h i j k) endE06M endX06M = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6M j), fun j ↦ hX (x0idx6M j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6M a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`141` monoid of `Magma.endE6M`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6M {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6M i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6M j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6M i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6M
    (fun k ↦ (Magma.end6M_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6M_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
