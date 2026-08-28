import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AG` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `180` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6AG0 : Fin 6 → Fin 6 := id
def pE6AG1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AG2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AG3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AG4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AG5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6AG6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6AG7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AG8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AG9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AG10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AG11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6AG : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6AG0
  | 1 => pE6AG1
  | 2 => pE6AG2
  | 3 => pE6AG3
  | 4 => pE6AG4
  | 5 => pE6AG5
  | 6 => pE6AG6
  | 7 => pE6AG7
  | 8 => pE6AG8
  | 9 => pE6AG9
  | 10 => pE6AG10
  | 11 => pE6AG11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `180` self-maps that must be endomorphisms: `222220`, `222320`, `222420`,
`222520`, `222230`, `222430`, `222530`, `222240`, `222340`, `222540`, `222250`, `222350`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AG : Fin 180 → Fin 46656
  | 0 => 3110
  | 1 => 3326
  | 2 => 3542
  | 3 => 3758
  | 4 => 4406
  | 5 => 4838
  | 6 => 5054
  | 7 => 5702
  | 8 => 5918
  | 9 => 6350
  | 10 => 6998
  | 11 => 7214
  | 12 => 7430
  | 13 => 10886
  | 14 => 11102
  | 15 => 11318
  | 16 => 11534
  | 17 => 12182
  | 18 => 12614
  | 19 => 12830
  | 20 => 13478
  | 21 => 13694
  | 22 => 14126
  | 23 => 14774
  | 24 => 14990
  | 25 => 15206
  | 26 => 16070
  | 27 => 16286
  | 28 => 16502
  | 29 => 16718
  | 30 => 17366
  | 31 => 17582
  | 32 => 17798
  | 33 => 18014
  | 34 => 18230
  | 35 => 18446
  | 36 => 18649
  | 37 => 18654
  | 38 => 18662
  | 39 => 18865
  | 40 => 18870
  | 41 => 18878
  | 42 => 19081
  | 43 => 19086
  | 44 => 19094
  | 45 => 19297
  | 46 => 19302
  | 47 => 19310
  | 48 => 19526
  | 49 => 19742
  | 50 => 19945
  | 51 => 19950
  | 52 => 19958
  | 53 => 20377
  | 54 => 20382
  | 55 => 20390
  | 56 => 20593
  | 57 => 20598
  | 58 => 20606
  | 59 => 20822
  | 60 => 21038
  | 61 => 21241
  | 62 => 21246
  | 63 => 21254
  | 64 => 21457
  | 65 => 21462
  | 66 => 21470
  | 67 => 21889
  | 68 => 21894
  | 69 => 21902
  | 70 => 22118
  | 71 => 22334
  | 72 => 22537
  | 73 => 22542
  | 74 => 22550
  | 75 => 22753
  | 76 => 22758
  | 77 => 22766
  | 78 => 22969
  | 79 => 22974
  | 80 => 22982
  | 81 => 23846
  | 82 => 24278
  | 83 => 24494
  | 84 => 25142
  | 85 => 25574
  | 86 => 25790
  | 87 => 26006
  | 88 => 26222
  | 89 => 26425
  | 90 => 26430
  | 91 => 26438
  | 92 => 26857
  | 93 => 26862
  | 94 => 26870
  | 95 => 27073
  | 96 => 27078
  | 97 => 27086
  | 98 => 28598
  | 99 => 28814
  | 100 => 29017
  | 101 => 29022
  | 102 => 29030
  | 103 => 29665
  | 104 => 29670
  | 105 => 29678
  | 106 => 29894
  | 107 => 30110
  | 108 => 30313
  | 109 => 30318
  | 110 => 30326
  | 111 => 30745
  | 112 => 30750
  | 113 => 30758
  | 114 => 31622
  | 115 => 31838
  | 116 => 32270
  | 117 => 32918
  | 118 => 33134
  | 119 => 33566
  | 120 => 33782
  | 121 => 33998
  | 122 => 34201
  | 123 => 34206
  | 124 => 34214
  | 125 => 34417
  | 126 => 34422
  | 127 => 34430
  | 128 => 34849
  | 129 => 34854
  | 130 => 34862
  | 131 => 35078
  | 132 => 35294
  | 133 => 35497
  | 134 => 35502
  | 135 => 35510
  | 136 => 36145
  | 137 => 36150
  | 138 => 36158
  | 139 => 37670
  | 140 => 37886
  | 141 => 38089
  | 142 => 38094
  | 143 => 38102
  | 144 => 38305
  | 145 => 38310
  | 146 => 38318
  | 147 => 39398
  | 148 => 39614
  | 149 => 39830
  | 150 => 40694
  | 151 => 40910
  | 152 => 41126
  | 153 => 41558
  | 154 => 41774
  | 155 => 41977
  | 156 => 41982
  | 157 => 41990
  | 158 => 42193
  | 159 => 42198
  | 160 => 42206
  | 161 => 42409
  | 162 => 42414
  | 163 => 42422
  | 164 => 42854
  | 165 => 43070
  | 166 => 43273
  | 167 => 43278
  | 168 => 43286
  | 169 => 43705
  | 170 => 43710
  | 171 => 43718
  | 172 => 44150
  | 173 => 44366
  | 174 => 44569
  | 175 => 44574
  | 176 => 44582
  | 177 => 44785
  | 178 => 44790
  | _ => 44798

def endE6AG (j : Fin 180) : Fin 6 → Fin 6 := allMaps6 (eidx6AG j)

/-- Indices of the other `46476`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AG : Array Nat := #[
  3110, 3326, 3542, 3758, 4406, 4838, 5054, 5702, 5918, 6350, 6998, 7214, 7430, 10886, 11102,
  11318, 11534, 12182, 12614, 12830, 13478, 13694, 14126, 14774, 14990, 15206, 16070, 16286,
  16502, 16718, 17366, 17582, 17798, 18014, 18230, 18446, 18649, 18654, 18662, 18865, 18870,
  18878, 19081, 19086, 19094, 19297, 19302, 19310, 19526, 19742, 19945, 19950, 19958, 20377,
  20382, 20390, 20593, 20598, 20606, 20822, 21038, 21241, 21246, 21254, 21457, 21462, 21470,
  21889, 21894, 21902, 22118, 22334, 22537, 22542, 22550, 22753, 22758, 22766, 22969, 22974,
  22982, 23846, 24278, 24494, 25142, 25574, 25790, 26006, 26222, 26425, 26430, 26438, 26857,
  26862, 26870, 27073, 27078, 27086, 28598, 28814, 29017, 29022, 29030, 29665, 29670, 29678,
  29894, 30110, 30313, 30318, 30326, 30745, 30750, 30758, 31622, 31838, 32270, 32918, 33134,
  33566, 33782, 33998, 34201, 34206, 34214, 34417, 34422, 34430, 34849, 34854, 34862, 35078,
  35294, 35497, 35502, 35510, 36145, 36150, 36158, 37670, 37886, 38089, 38094, 38102, 38305,
  38310, 38318, 39398, 39614, 39830, 40694, 40910, 41126, 41558, 41774, 41977, 41982, 41990,
  42193, 42198, 42206, 42409, 42414, 42422, 42854, 43070, 43273, 43278, 43286, 43705, 43710,
  43718, 44150, 44366, 44569, 44574, 44582, 44785, 44790, 44798]

def xarr6AG : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AG.contains i)

def xidx6AG (j : Fin 46476) : Fin 46656 :=
  ⟨min (xarr6AG.getD j.1 0) 46655, by omega⟩

def endX6AG (j : Fin 46476) : Fin 6 → Fin 6 := allMaps6 (xidx6AG j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AG` is given. -/
def uidx6AG : Fin 12 → Fin 180
  | 0 => 178
  | 1 => 145
  | 2 => 170
  | 3 => 112
  | 4 => 137
  | 5 => 104
  | 6 => 177
  | 7 => 144
  | 8 => 169
  | 9 => 111
  | 10 => 136
  | 11 => 103

theorem permE6AG_eq_endE6AG (i : Fin 12) : permE6AG i = endE6AG (uidx6AG i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6AG : Fin 11 → Fin 6 × Fin 6
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
def tr6AG : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6AG0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AG0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AG1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AG1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AG2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AG2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AG3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AG3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AG4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AG4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6AG5 : Fin 12 → Fin 12
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
def val6AG5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AG6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AG6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AG7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AG7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AG8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AG8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AG9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AG9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AG10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6AG10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6AG (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6AG0 a
  | 1 => val6AG1 b
  | 2 => val6AG2 c
  | 3 => val6AG3 d
  | 4 => val6AG4 e
  | 5 => val6AG5 f
  | 6 => val6AG6 g
  | 7 => val6AG7 h
  | 8 => val6AG8 i
  | 9 => val6AG9 j
  | 10 => val6AG10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AG_eq_transport`). -/
def tab6AG (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AG0 a
  | 0, 1 => val6AG1 b
  | 0, 2 => val6AG2 c
  | 0, 3 => val6AG3 d
  | 0, 4 => pE6AG2 (val6AG3 d)
  | 0, 5 => pE6AG4 (val6AG3 d)
  | 1, 0 => pE6AG6 (val6AG1 b)
  | 1, 1 => pE6AG6 (val6AG0 a)
  | 1, 2 => pE6AG6 (val6AG2 c)
  | 1, 3 => pE6AG6 (val6AG3 d)
  | 1, 4 => pE6AG8 (val6AG3 d)
  | 1, 5 => pE6AG10 (val6AG3 d)
  | 2, 0 => val6AG4 e
  | 2, 1 => pE6AG6 (val6AG4 e)
  | 2, 2 => val6AG5 f
  | 2, 3 => val6AG6 g
  | 2, 4 => pE6AG2 (val6AG6 g)
  | 2, 5 => pE6AG4 (val6AG6 g)
  | 3, 0 => val6AG7 h
  | 3, 1 => pE6AG6 (val6AG7 h)
  | 3, 2 => val6AG8 i
  | 3, 3 => val6AG9 j
  | 3, 4 => val6AG10 k
  | 3, 5 => pE6AG1 (val6AG10 k)
  | 4, 0 => pE6AG2 (val6AG7 h)
  | 4, 1 => pE6AG8 (val6AG7 h)
  | 4, 2 => pE6AG2 (val6AG8 i)
  | 4, 3 => pE6AG2 (val6AG10 k)
  | 4, 4 => pE6AG2 (val6AG9 j)
  | 4, 5 => pE6AG3 (val6AG10 k)
  | 5, 0 => pE6AG4 (val6AG7 h)
  | 5, 1 => pE6AG10 (val6AG7 h)
  | 5, 2 => pE6AG4 (val6AG8 i)
  | 5, 3 => pE6AG4 (val6AG10 k)
  | 5, 4 => pE6AG5 (val6AG10 k)
  | 5, 5 => pE6AG4 (val6AG9 j)

theorem tab6AG_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6AG a b c d e f g h i j k = Magma.transport permE6AG tr6AG (dec6AG a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AG : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AG 2 0 2 3 0 0 1 0 0 0 2
  | 1 => tab6AG 2 1 0 0 2 0 0 3 1 0 1

/-- The arguments as one mixed-radix index, which is how `rankIdx6AG` is addressed. -/
def encT6AG (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
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

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6AG` can name one
rather than search the list for it. The `41470` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6AG` excludes them. Read only by `native_decide`. -/
def rankIdx6AG : Nat → Nat
  | 31938 => 0
  | 32569 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AG (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4) : Fin 2 :=
  ⟨min (rankIdx6AG (encT6AG a b c d e f g h i j k)) 1, by omega⟩


/-- `1` of the `180` demanded maps and `4` of the `46476` forbidden ones, enough to separate the `2`
members from the other `41470` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AG` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AG : Fin 1 → Fin 180
  | 0 => 1
def x0idx6AG : Fin 4 → Fin 46476
  | 0 => 0
  | 1 => 86
  | 2 => 1814
  | 3 => 3116

def endE06AG (j : Fin 1) : Fin 6 → Fin 6 := endE6AG (e0idx6AG j)

def endX06AG (j : Fin 4) : Fin 6 → Fin 6 := endX6AG (x0idx6AG j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AG (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6AG i)

theorem end6AG_isEndo (i : Fin 2) (j : Fin 180) : (end6AG i).IsEndo (endE6AG j) := by
  revert i j; native_decide

theorem end6AG_not_isEndo (i : Fin 2) (j : Fin 46476) : ¬ (end6AG i).IsEndo (endX6AG j) := by
  revert i j; native_decide

/-- `rank6AG` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AG` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AG (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AG a b c d e f g h i j k) endE06AG endX06AG = true) :
    mem6AG (rank6AG a b c d e f g h i j k) = tab6AG a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6AG (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AG a b c d e f g h i j k) endE06AG endX06AG = true) :
    ∃ idx, mem6AG idx = tab6AG a b c d e f g h i j k :=
  ⟨_, mem_rank6AG a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AG`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AG` turns that into a member index. -/
theorem exists_end6AG {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AG j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AG j)) : ∃ i, end6AG i = M := by
  have hP : ∀ i, M.IsEndo (permE6AG i) := by
    intro i; rw [permE6AG_eq_endE6AG]; exact hE (uidx6AG i)
  have hop : M.op = Magma.transport permE6AG tr6AG (fun i ↦ M.op (rep6AG i).1 (rep6AG i).2) :=
    Magma.op_eq_transport (rep := rep6AG) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG0) (a := (rep6AG 0).1) (b := (rep6AG 0).2)
    (val := val6AG0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG1) (a := (rep6AG 1).1) (b := (rep6AG 1).2)
    (val := val6AG1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG2) (a := (rep6AG 2).1) (b := (rep6AG 2).2)
    (val := val6AG2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG3) (a := (rep6AG 3).1) (b := (rep6AG 3).2)
    (val := val6AG3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG4) (a := (rep6AG 4).1) (b := (rep6AG 4).2)
    (val := val6AG4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG5) (a := (rep6AG 5).1) (b := (rep6AG 5).2)
    (val := val6AG5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG6) (a := (rep6AG 6).1) (b := (rep6AG 6).2)
    (val := val6AG6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG7) (a := (rep6AG 7).1) (b := (rep6AG 7).2)
    (val := val6AG7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG8) (a := (rep6AG 8).1) (b := (rep6AG 8).2)
    (val := val6AG8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG9) (a := (rep6AG 9).1) (b := (rep6AG 9).2)
    (val := val6AG9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6AG) (idx := stabIdx6AG10) (a := (rep6AG 10).1) (b := (rep6AG 10).2)
    (val := val6AG10) hP (by decide) (by decide)
  have hdec : dec6AG a b c d e f g h i j k = fun i ↦ M.op (rep6AG i).1 (rep6AG i).2 := by
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
  have key : tab6AG a b c d e f g h i j k = M.op := by
    rw [tab6AG_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AG a b c d e f g h i j k) endE06AG endX06AG = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AG j), fun j ↦ hX (x0idx6AG j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AG a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`180` monoid of `Magma.endE6AG`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AG {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AG i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AG j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AG i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AG
    (fun k ↦ (Magma.end6AG_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AG_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
