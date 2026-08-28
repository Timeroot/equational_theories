import equational_theories.Definability.ExactEnd7

/-!
# The exact-endomorphism class `B` on `Fin 7`

One class of `Definability/ExactEnd7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `24`: `⟨(0 1)(2 3)(4 5 6), (0 2)(1 3)(5 6), (0 2 1 3)(5 6)⟩`

`End(M)` is `223` maps, so `Aut(M)` -- its unit group -- is these `24` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `7` orbit values rather than `49`
independent cells. -/

/-- The `24` elements of the group: `()`, `(4 5 6)`, `(4 6 5)`, `(2 3)`, `(2 3)(4 5 6)`, `(2 3)(4 6
5)`, `(0 1)`, `(0 1)(4 5 6)`, `(0 1)(4 6 5)`, `(0 1)(2 3)`, `(0 1)(2 3)(4 5 6)`, `(0 1)(2 3)(4 6
5)`, `(0 2)(1 3)(5 6)`, `(0 2)(1 3)(4 5)`, `(0 2)(1 3)(4 6)`, `(0 2 1 3)(5 6)`, `(0 2 1 3)(4 5)`,
`(0 2 1 3)(4 6)`, `(0 3 1 2)(5 6)`, `(0 3 1 2)(4 5)`, `(0 3 1 2)(4 6)`, `(0 3)(1 2)(5 6)`, `(0 3)(1
2)(4 5)`, `(0 3)(1 2)(4 6)`. -/
def pE7B0 : Fin 7 → Fin 7 := id
def pE7B1 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 4
def pE7B2 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 4 | 6 => 5
def pE7B3 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6
def pE7B4 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4
def pE7B5 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5
def pE7B6 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6
def pE7B7 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 4
def pE7B8 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 4 | 6 => 5
def pE7B9 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6
def pE7B10 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4
def pE7B11 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5
def pE7B12 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5
def pE7B13 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6
def pE7B14 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4
def pE7B15 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5
def pE7B16 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 6
def pE7B17 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4
def pE7B18 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5
def pE7B19 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6
def pE7B20 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4
def pE7B21 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5
def pE7B22 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 6
def pE7B23 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4

def permE7B : Fin 24 → Fin 7 → Fin 7
  | 0 => pE7B0
  | 1 => pE7B1
  | 2 => pE7B2
  | 3 => pE7B3
  | 4 => pE7B4
  | 5 => pE7B5
  | 6 => pE7B6
  | 7 => pE7B7
  | 8 => pE7B8
  | 9 => pE7B9
  | 10 => pE7B10
  | 11 => pE7B11
  | 12 => pE7B12
  | 13 => pE7B13
  | 14 => pE7B14
  | 15 => pE7B15
  | 16 => pE7B16
  | 17 => pE7B17
  | 18 => pE7B18
  | 19 => pE7B19
  | 20 => pE7B20
  | 21 => pE7B21
  | 22 => pE7B22
  | _ => pE7B23

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `823543` self-maps of `Fin 7`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps7` indexes the self-maps, digit by digit. -/

/-- Indices of the `223` self-maps that must be endomorphisms: `0000000`, `1111111`, `2222222`,
`3333333`, `3210444`, `2310444`, `3201444`, `2301444`, `1032444`, `0132444`, `1023444`, `0123444`,
... (each written as its list of values at `0, 1, ..., 6`). -/
def eidx7B : Fin 223 → Fin 823543
  | 0 => 0
  | 1 => 137257
  | 2 => 274514
  | 3 => 411771
  | 4 => 547494
  | 5 => 547500
  | 6 => 547788
  | 7 => 547794
  | 8 => 548262
  | 9 => 548268
  | 10 => 548556
  | 11 => 548562
  | 12 => 549028
  | 13 => 549895
  | 14 => 549901
  | 15 => 550189
  | 16 => 550195
  | 17 => 550663
  | 18 => 550669
  | 19 => 550957
  | 20 => 550963
  | 21 => 552296
  | 22 => 552302
  | 23 => 552590
  | 24 => 552596
  | 25 => 553064
  | 26 => 553070
  | 27 => 553358
  | 28 => 553364
  | 29 => 564301
  | 30 => 564307
  | 31 => 564595
  | 32 => 564601
  | 33 => 565069
  | 34 => 565075
  | 35 => 565363
  | 36 => 565369
  | 37 => 566702
  | 38 => 566708
  | 39 => 566996
  | 40 => 567002
  | 41 => 567470
  | 42 => 567476
  | 43 => 567764
  | 44 => 567770
  | 45 => 569103
  | 46 => 569109
  | 47 => 569397
  | 48 => 569403
  | 49 => 569871
  | 50 => 569877
  | 51 => 570165
  | 52 => 570171
  | 53 => 581108
  | 54 => 581114
  | 55 => 581402
  | 56 => 581408
  | 57 => 581876
  | 58 => 581882
  | 59 => 582170
  | 60 => 582176
  | 61 => 583509
  | 62 => 583515
  | 63 => 583803
  | 64 => 583809
  | 65 => 584277
  | 66 => 584283
  | 67 => 584571
  | 68 => 584577
  | 69 => 585910
  | 70 => 585916
  | 71 => 586204
  | 72 => 586210
  | 73 => 586678
  | 74 => 586684
  | 75 => 586972
  | 76 => 586978
  | 77 => 665143
  | 78 => 665149
  | 79 => 665437
  | 80 => 665443
  | 81 => 665911
  | 82 => 665917
  | 83 => 666205
  | 84 => 666211
  | 85 => 667544
  | 86 => 667550
  | 87 => 667838
  | 88 => 667844
  | 89 => 668312
  | 90 => 668318
  | 91 => 668606
  | 92 => 668612
  | 93 => 669945
  | 94 => 669951
  | 95 => 670239
  | 96 => 670245
  | 97 => 670713
  | 98 => 670719
  | 99 => 671007
  | 100 => 671013
  | 101 => 681950
  | 102 => 681956
  | 103 => 682244
  | 104 => 682250
  | 105 => 682718
  | 106 => 682724
  | 107 => 683012
  | 108 => 683018
  | 109 => 684351
  | 110 => 684357
  | 111 => 684645
  | 112 => 684651
  | 113 => 685119
  | 114 => 685125
  | 115 => 685413
  | 116 => 685419
  | 117 => 686285
  | 118 => 686752
  | 119 => 686758
  | 120 => 687046
  | 121 => 687052
  | 122 => 687520
  | 123 => 687526
  | 124 => 687814
  | 125 => 687820
  | 126 => 698757
  | 127 => 698763
  | 128 => 699051
  | 129 => 699057
  | 130 => 699525
  | 131 => 699531
  | 132 => 699819
  | 133 => 699825
  | 134 => 701158
  | 135 => 701164
  | 136 => 701452
  | 137 => 701458
  | 138 => 701926
  | 139 => 701932
  | 140 => 702220
  | 141 => 702226
  | 142 => 703559
  | 143 => 703565
  | 144 => 703853
  | 145 => 703859
  | 146 => 704327
  | 147 => 704333
  | 148 => 704621
  | 149 => 704627
  | 150 => 782792
  | 151 => 782798
  | 152 => 783086
  | 153 => 783092
  | 154 => 783560
  | 155 => 783566
  | 156 => 783854
  | 157 => 783860
  | 158 => 785193
  | 159 => 785199
  | 160 => 785487
  | 161 => 785493
  | 162 => 785961
  | 163 => 785967
  | 164 => 786255
  | 165 => 786261
  | 166 => 787594
  | 167 => 787600
  | 168 => 787888
  | 169 => 787894
  | 170 => 788362
  | 171 => 788368
  | 172 => 788656
  | 173 => 788662
  | 174 => 799599
  | 175 => 799605
  | 176 => 799893
  | 177 => 799899
  | 178 => 800367
  | 179 => 800373
  | 180 => 800661
  | 181 => 800667
  | 182 => 802000
  | 183 => 802006
  | 184 => 802294
  | 185 => 802300
  | 186 => 802768
  | 187 => 802774
  | 188 => 803062
  | 189 => 803068
  | 190 => 804401
  | 191 => 804407
  | 192 => 804695
  | 193 => 804701
  | 194 => 805169
  | 195 => 805175
  | 196 => 805463
  | 197 => 805469
  | 198 => 816406
  | 199 => 816412
  | 200 => 816700
  | 201 => 816706
  | 202 => 817174
  | 203 => 817180
  | 204 => 817468
  | 205 => 817474
  | 206 => 818807
  | 207 => 818813
  | 208 => 819101
  | 209 => 819107
  | 210 => 819575
  | 211 => 819581
  | 212 => 819869
  | 213 => 819875
  | 214 => 821208
  | 215 => 821214
  | 216 => 821502
  | 217 => 821508
  | 218 => 821976
  | 219 => 821982
  | 220 => 822270
  | 221 => 822276
  | _ => 823542

def endE7B (j : Fin 223) : Fin 7 → Fin 7 := allMaps7 (eidx7B j)

/-- Indices of the other `823320`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset7B : Array Nat := #[
  0, 137257, 274514, 411771, 547494, 547500, 547788, 547794, 548262, 548268, 548556, 548562,
  549028, 549895, 549901, 550189, 550195, 550663, 550669, 550957, 550963, 552296, 552302, 552590,
  552596, 553064, 553070, 553358, 553364, 564301, 564307, 564595, 564601, 565069, 565075, 565363,
  565369, 566702, 566708, 566996, 567002, 567470, 567476, 567764, 567770, 569103, 569109, 569397,
  569403, 569871, 569877, 570165, 570171, 581108, 581114, 581402, 581408, 581876, 581882, 582170,
  582176, 583509, 583515, 583803, 583809, 584277, 584283, 584571, 584577, 585910, 585916, 586204,
  586210, 586678, 586684, 586972, 586978, 665143, 665149, 665437, 665443, 665911, 665917, 666205,
  666211, 667544, 667550, 667838, 667844, 668312, 668318, 668606, 668612, 669945, 669951, 670239,
  670245, 670713, 670719, 671007, 671013, 681950, 681956, 682244, 682250, 682718, 682724, 683012,
  683018, 684351, 684357, 684645, 684651, 685119, 685125, 685413, 685419, 686285, 686752, 686758,
  687046, 687052, 687520, 687526, 687814, 687820, 698757, 698763, 699051, 699057, 699525, 699531,
  699819, 699825, 701158, 701164, 701452, 701458, 701926, 701932, 702220, 702226, 703559, 703565,
  703853, 703859, 704327, 704333, 704621, 704627, 782792, 782798, 783086, 783092, 783560, 783566,
  783854, 783860, 785193, 785199, 785487, 785493, 785961, 785967, 786255, 786261, 787594, 787600,
  787888, 787894, 788362, 788368, 788656, 788662, 799599, 799605, 799893, 799899, 800367, 800373,
  800661, 800667, 802000, 802006, 802294, 802300, 802768, 802774, 803062, 803068, 804401, 804407,
  804695, 804701, 805169, 805175, 805463, 805469, 816406, 816412, 816700, 816706, 817174, 817180,
  817468, 817474, 818807, 818813, 819101, 819107, 819575, 819581, 819869, 819875, 821208, 821214,
  821502, 821508, 821976, 821982, 822270, 822276, 823542]

def xarr7B : Array Nat := Id.run do
  let mut out := Array.mkEmpty 823320
  let mut k := 0
  for i in [0:823543] do
    if k < eset7B.size && eset7B[k]! == i then
      k := k + 1
    else
      out := out.push i
  return out

def xidx7B (j : Fin 823320) : Fin 823543 :=
  ⟨min (xarr7B.getD j.1 0) 823542, by omega⟩

def endX7B (j : Fin 823320) : Fin 7 → Fin 7 := allMaps7 (xidx7B j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end7B` is given. -/
def uidx7B : Fin 24 → Fin 223
  | 0 => 181
  | 1 => 68
  | 2 => 100
  | 3 => 179
  | 4 => 66
  | 5 => 98
  | 6 => 180
  | 7 => 67
  | 8 => 99
  | 9 => 178
  | 10 => 65
  | 11 => 97
  | 12 => 129
  | 13 => 161
  | 14 => 48
  | 15 => 127
  | 16 => 159
  | 17 => 46
  | 18 => 128
  | 19 => 160
  | 20 => 47
  | 21 => 126
  | 22 => 158
  | _ => 45

theorem permE7B_eq_endE7B (i : Fin 24) : permE7B i = endE7B (uidx7B i) := by
  revert i; decide

/-- One representative per orbit of the group on the `49` cells; there are `7`, so an invariant
operation is `7` values. -/
def rep7B : Fin 7 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (4, 0)
  | 5 => (4, 4)
  | 6 => (4, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr7B : Fin 7 → Fin 7 → Fin 7 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 3)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 0, 6 => (3, 2)
  | 1, 0 => (1, 6)
  | 1, 1 => (0, 6)
  | 1, 2 => (2, 6)
  | 1, 3 => (2, 9)
  | 1, 4 => (3, 6)
  | 1, 5 => (3, 7)
  | 1, 6 => (3, 8)
  | 2, 0 => (2, 12)
  | 2, 1 => (2, 15)
  | 2, 2 => (0, 12)
  | 2, 3 => (1, 12)
  | 2, 4 => (3, 12)
  | 2, 5 => (3, 13)
  | 2, 6 => (3, 14)
  | 3, 0 => (2, 18)
  | 3, 1 => (2, 21)
  | 3, 2 => (1, 18)
  | 3, 3 => (0, 18)
  | 3, 4 => (3, 18)
  | 3, 5 => (3, 19)
  | 3, 6 => (3, 20)
  | 4, 0 => (4, 0)
  | 4, 1 => (4, 6)
  | 4, 2 => (4, 12)
  | 4, 3 => (4, 18)
  | 4, 4 => (5, 0)
  | 4, 5 => (6, 0)
  | 4, 6 => (6, 12)
  | 5, 0 => (4, 1)
  | 5, 1 => (4, 7)
  | 5, 2 => (4, 13)
  | 5, 3 => (4, 19)
  | 5, 4 => (6, 13)
  | 5, 5 => (5, 1)
  | 5, 6 => (6, 1)
  | 6, 0 => (4, 2)
  | 6, 1 => (4, 8)
  | 6, 2 => (4, 14)
  | 6, 3 => (4, 20)
  | 6, 4 => (6, 2)
  | 6, 5 => (6, 14)
  | 6, 6 => (5, 2)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx7B0 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val7B0 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx7B1 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val7B1 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 1

/-- The `3` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx7B2 : Fin 3 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
def val7B2 : Fin 4 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `4`, `5`, `6`, so the orbit is indexed by `Fin 5`
instead. -/
def stabIdx7B3 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 3
def val7B3 : Fin 5 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 6

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `4`, `5`, `6`, so the orbit is indexed by `Fin 5`
instead. -/
def stabIdx7B4 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 3
def val7B4 : Fin 5 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 6

/-- The `8` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `4`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx7B5 : Fin 8 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 6
  | 3 => 9
  | 4 => 12
  | 5 => 15
  | 6 => 18
  | 7 => 21
def val7B5 : Fin 1 → Fin 7
  | 0 => 4

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `4`, `5`, `6`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx7B6 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 6
  | 3 => 9
def val7B6 : Fin 3 → Fin 7
  | 0 => 4
  | 1 => 5
  | 2 => 6

/-- The `7` orbit values named by the family's arguments. -/
def dec7B (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Fin 7 → Fin 7
  | 0 => val7B0 a
  | 1 => val7B1 b
  | 2 => val7B2 c
  | 3 => val7B3 d
  | 4 => val7B4 e
  | 5 => val7B5 f
  | 6 => val7B6 g

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab7B_eq_transport`). -/
def tab7B (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => val7B0 a
  | 0, 1 => val7B1 b
  | 0, 2 => val7B2 c
  | 0, 3 => pE7B3 (val7B2 c)
  | 0, 4 => val7B3 d
  | 0, 5 => pE7B1 (val7B3 d)
  | 0, 6 => pE7B2 (val7B3 d)
  | 1, 0 => pE7B6 (val7B1 b)
  | 1, 1 => pE7B6 (val7B0 a)
  | 1, 2 => pE7B6 (val7B2 c)
  | 1, 3 => pE7B9 (val7B2 c)
  | 1, 4 => pE7B6 (val7B3 d)
  | 1, 5 => pE7B7 (val7B3 d)
  | 1, 6 => pE7B8 (val7B3 d)
  | 2, 0 => pE7B12 (val7B2 c)
  | 2, 1 => pE7B15 (val7B2 c)
  | 2, 2 => pE7B12 (val7B0 a)
  | 2, 3 => pE7B12 (val7B1 b)
  | 2, 4 => pE7B12 (val7B3 d)
  | 2, 5 => pE7B13 (val7B3 d)
  | 2, 6 => pE7B14 (val7B3 d)
  | 3, 0 => pE7B18 (val7B2 c)
  | 3, 1 => pE7B21 (val7B2 c)
  | 3, 2 => pE7B18 (val7B1 b)
  | 3, 3 => pE7B18 (val7B0 a)
  | 3, 4 => pE7B18 (val7B3 d)
  | 3, 5 => pE7B19 (val7B3 d)
  | 3, 6 => pE7B20 (val7B3 d)
  | 4, 0 => val7B4 e
  | 4, 1 => pE7B6 (val7B4 e)
  | 4, 2 => pE7B12 (val7B4 e)
  | 4, 3 => pE7B18 (val7B4 e)
  | 4, 4 => val7B5 f
  | 4, 5 => val7B6 g
  | 4, 6 => pE7B12 (val7B6 g)
  | 5, 0 => pE7B1 (val7B4 e)
  | 5, 1 => pE7B7 (val7B4 e)
  | 5, 2 => pE7B13 (val7B4 e)
  | 5, 3 => pE7B19 (val7B4 e)
  | 5, 4 => pE7B13 (val7B6 g)
  | 5, 5 => pE7B1 (val7B5 f)
  | 5, 6 => pE7B1 (val7B6 g)
  | 6, 0 => pE7B2 (val7B4 e)
  | 6, 1 => pE7B8 (val7B4 e)
  | 6, 2 => pE7B14 (val7B4 e)
  | 6, 3 => pE7B20 (val7B4 e)
  | 6, 4 => pE7B2 (val7B6 g)
  | 6, 5 => pE7B14 (val7B6 g)
  | 6, 6 => pE7B2 (val7B5 f)

theorem tab7B_eq_transport (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) :
    tab7B a b c d e f g = Magma.transport permE7B tr7B (dec7B a b c d e f g) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `38` magmas on `Fin 7` whose endomorphism monoid is exactly this one, listed under one
index. Of the `1200` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem7B : Fin 38 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7B 0 0 1 0 1 0 0
  | 1 => tab7B 0 0 1 0 1 0 1
  | 2 => tab7B 0 0 1 1 0 0 0
  | 3 => tab7B 0 0 1 1 0 0 1
  | 4 => tab7B 0 0 1 1 1 0 0
  | 5 => tab7B 0 0 1 1 1 0 1
  | 6 => tab7B 0 0 1 2 1 0 0
  | 7 => tab7B 0 0 2 0 1 0 0
  | 8 => tab7B 0 0 2 0 1 0 1
  | 9 => tab7B 0 0 2 1 0 0 0
  | 10 => tab7B 0 0 2 1 0 0 1
  | 11 => tab7B 0 0 2 1 1 0 0
  | 12 => tab7B 0 0 2 1 1 0 1
  | 13 => tab7B 0 0 3 0 1 0 0
  | 14 => tab7B 0 0 3 0 1 0 1
  | 15 => tab7B 0 0 3 1 0 0 0
  | 16 => tab7B 0 0 3 1 0 0 1
  | 17 => tab7B 0 0 3 1 1 0 0
  | 18 => tab7B 0 0 3 1 1 0 1
  | 19 => tab7B 0 1 0 0 1 0 0
  | 20 => tab7B 0 1 0 0 1 0 1
  | 21 => tab7B 0 1 0 1 0 0 0
  | 22 => tab7B 0 1 0 1 0 0 1
  | 23 => tab7B 0 1 0 1 1 0 0
  | 24 => tab7B 0 1 0 1 1 0 1
  | 25 => tab7B 0 1 1 0 1 0 0
  | 26 => tab7B 0 1 1 0 1 0 1
  | 27 => tab7B 0 1 1 1 0 0 0
  | 28 => tab7B 0 1 1 1 0 0 1
  | 29 => tab7B 0 1 1 1 1 0 0
  | 30 => tab7B 0 1 1 1 1 0 1
  | 31 => tab7B 0 1 3 0 1 0 0
  | 32 => tab7B 0 1 3 0 1 0 1
  | 33 => tab7B 0 1 3 1 0 0 0
  | 34 => tab7B 0 1 3 1 0 0 1
  | 35 => tab7B 0 1 3 1 1 0 0
  | 36 => tab7B 0 1 3 1 1 0 1
  | _ => tab7B 0 1 3 1 2 0 1

/-- Which of the `38` members a given invariant tuple is, so that `mem_of_isExact7B` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr7B : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 4, 5, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 8, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 9, 10, 0, 11, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 13, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 0, 17, 18, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21,
  22, 0, 23, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  25, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 28, 0, 29, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 32, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 33, 34, 0, 35, 36, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr7B` is addressed. -/
def encT7B (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Nat :=
  a.1 * 600 +
    b.1 * 300 +
    c.1 * 75 +
    d.1 * 15 +
    e.1 * 3 +
    f.1 * 3 +
    g.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank7B (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Fin 38 :=
  ⟨min (rankArr7B.getD (encT7B a b c d e f g) 0) 37, by omega⟩


/-- `2` of the `223` demanded maps and `6` of the `823320` forbidden ones, enough to separate the
`38` members from the other `1162` invariant tuples between them. The certificate demands all `223`
-- the group has to be among them -- but forbids only these: `mem_rank7B` scans them once per tuple
with a scan quadratic in their length, and nothing else reads the forbidden side. -/
def e0idx7B : Fin 2 → Fin 223
  | 0 => 0
  | 1 => 13
def x0idx7B : Fin 6 → Fin 823320
  | 0 => 15
  | 1 => 399
  | 2 => 547424
  | 3 => 547474
  | 4 => 547503
  | 5 => 549415

def endE07B (j : Fin 2) : Fin 7 → Fin 7 := endE7B (e0idx7B j)

def endX07B (j : Fin 6) : Fin 7 → Fin 7 := endX7B (x0idx7B j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end7B (i : Fin 38) : Magma (Fin 7) := Magma.mk (mem7B i)

theorem end7B_isEndo (i : Fin 38) (j : Fin 223) : (end7B i).IsEndo (endE7B j) := by
  revert i j; native_decide

theorem end7B_not_isEndo (i : Fin 38) (j : Fin 6) : ¬ (end7B i).IsEndo (endX07B j) := by
  revert i j; native_decide

/-- `rank7B` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem7B` for the index would be a comparison per tuple and
member. -/
theorem mem_rank7B (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3)
    (hx : Magma.isExact (tab7B a b c d e f g) endE07B endX07B = true) :
    mem7B (rank7B a b c d e f g) = tab7B a b c d e f g := by
  revert hx; revert a b c d e f g; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `38` listed
members. -/
theorem mem_of_isExact7B (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3)
    (hx : Magma.isExact (tab7B a b c d e f g) endE07B endX07B = true) :
    ∃ idx, mem7B idx = tab7B a b c d e f g :=
  ⟨_, mem_rank7B a b c d e f g hx⟩

/-- A magma on `Fin 7` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end7B`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact7B` turns that into a member index. -/
theorem exists_end7B {M : Magma (Fin 7)} (hE : ∀ j, M.IsEndo (endE7B j))
    (hX : ∀ j, ¬ M.IsEndo (endX07B j)) : ∃ i, end7B i = M := by
  have hP : ∀ i, M.IsEndo (permE7B i) := by
    intro i; rw [permE7B_eq_endE7B]; exact hE (uidx7B i)
  have hop : M.op = Magma.transport permE7B tr7B (fun i ↦ M.op (rep7B i).1 (rep7B i).2) :=
    Magma.op_eq_transport (rep := rep7B) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B0) (a := (rep7B 0).1) (b := (rep7B 0).2)
    (val := val7B0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B1) (a := (rep7B 1).1) (b := (rep7B 1).2)
    (val := val7B1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B2) (a := (rep7B 2).1) (b := (rep7B 2).2)
    (val := val7B2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B3) (a := (rep7B 3).1) (b := (rep7B 3).2)
    (val := val7B3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B4) (a := (rep7B 4).1) (b := (rep7B 4).2)
    (val := val7B4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B5) (a := (rep7B 5).1) (b := (rep7B 5).2)
    (val := val7B5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE7B) (idx := stabIdx7B6) (a := (rep7B 6).1) (b := (rep7B 6).2)
    (val := val7B6) hP (by decide) (by decide)
  have hdec : dec7B a b c d e f g = fun i ↦ M.op (rep7B i).1 (rep7B i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
  have key : tab7B a b c d e f g = M.op := by
    rw [tab7B_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab7B a b c d e f g) endE07B endX07B = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx7B j), hX⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact7B a b c d e f g hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose endomorphism
monoid is exactly the order-`223` monoid of `Magma.endE7B`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end7B {L L' : Law.NatMagmaLaw} {i : Fin 38}
    (hsrc : @satisfies _ (Fin 7) (Magma.end7B i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.end7B j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end7B i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end7B
    (fun k ↦ (Magma.end7B_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end7B_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
