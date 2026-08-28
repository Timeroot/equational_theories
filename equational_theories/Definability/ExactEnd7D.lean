import equational_theories.Definability.ExactEnd7

/-!
# The exact-endomorphism class `D` on `Fin 7`

One class of `Definability/ExactEnd7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 3 4)(1 6)(2 5), (1 2)(3 4)(5 6)⟩`

`End(M)` is `351` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `8` orbit values rather than `49`
independent cells. -/

/-- The `12` elements of the group: `()`, `(1 2)(3 4)(5 6)`, `(1 5)(2 6)(3 4)`, `(1 6)(2 5)`, `(0 3
4)`, `(0 3)(1 2)(5 6)`, `(0 3)(1 5)(2 6)`, `(0 3 4)(1 6)(2 5)`, `(0 4 3)`, `(0 4)(1 2)(5 6)`, `(0
4)(1 5)(2 6)`, `(0 4 3)(1 6)(2 5)`. -/
def pE7D0 : Fin 7 → Fin 7 := id
def pE7D1 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pE7D2 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 2
def pE7D3 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 2 | 6 => 1
def pE7D4 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6
def pE7D5 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5
def pE7D6 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 6 | 3 => 0 | 4 => 4 | 5 => 1 | 6 => 2
def pE7D7 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 2 | 6 => 1
def pE7D8 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6
def pE7D9 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5
def pE7D10 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 3 | 4 => 0 | 5 => 1 | 6 => 2
def pE7D11 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 5 | 3 => 0 | 4 => 3 | 5 => 2 | 6 => 1

def permE7D : Fin 12 → Fin 7 → Fin 7
  | 0 => pE7D0
  | 1 => pE7D1
  | 2 => pE7D2
  | 3 => pE7D3
  | 4 => pE7D4
  | 5 => pE7D5
  | 6 => pE7D6
  | 7 => pE7D7
  | 8 => pE7D8
  | 9 => pE7D9
  | 10 => pE7D10
  | 11 => pE7D11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `823543` self-maps of `Fin 7`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps7` indexes the self-maps, digit by digit. -/

/-- Indices of the `351` self-maps that must be endomorphisms: `0000000`, `3000000`, `4000000`,
`0330000`, `3330000`, `4330000`, `0440000`, `3440000`, `4440000`, `0003000`, `3003000`, `4003000`,
... (each written as its list of values at `0, 1, ..., 6`). -/
def eidx7D : Fin 351 → Fin 823543
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 168
  | 4 => 171
  | 5 => 172
  | 6 => 224
  | 7 => 227
  | 8 => 228
  | 9 => 1029
  | 10 => 1032
  | 11 => 1033
  | 12 => 1197
  | 13 => 1200
  | 14 => 1201
  | 15 => 1253
  | 16 => 1256
  | 17 => 1257
  | 18 => 1372
  | 19 => 1375
  | 20 => 1376
  | 21 => 1540
  | 22 => 1543
  | 23 => 1544
  | 24 => 1596
  | 25 => 1599
  | 26 => 1600
  | 27 => 7203
  | 28 => 7206
  | 29 => 7207
  | 30 => 7371
  | 31 => 7374
  | 32 => 7375
  | 33 => 7427
  | 34 => 7430
  | 35 => 7431
  | 36 => 8232
  | 37 => 8235
  | 38 => 8236
  | 39 => 8400
  | 40 => 8403
  | 41 => 8404
  | 42 => 8456
  | 43 => 8459
  | 44 => 8460
  | 45 => 8575
  | 46 => 8578
  | 47 => 8579
  | 48 => 8743
  | 49 => 8746
  | 50 => 8747
  | 51 => 8799
  | 52 => 8802
  | 53 => 8803
  | 54 => 9604
  | 55 => 9607
  | 56 => 9608
  | 57 => 9772
  | 58 => 9775
  | 59 => 9776
  | 60 => 9828
  | 61 => 9831
  | 62 => 9832
  | 63 => 10633
  | 64 => 10636
  | 65 => 10637
  | 66 => 10801
  | 67 => 10804
  | 68 => 10805
  | 69 => 10857
  | 70 => 10860
  | 71 => 10861
  | 72 => 10976
  | 73 => 10979
  | 74 => 10980
  | 75 => 11144
  | 76 => 11147
  | 77 => 11148
  | 78 => 11200
  | 79 => 11203
  | 80 => 11204
  | 81 => 151550
  | 82 => 151553
  | 83 => 151554
  | 84 => 152579
  | 85 => 152582
  | 86 => 152583
  | 87 => 152922
  | 88 => 152925
  | 89 => 152926
  | 90 => 158753
  | 91 => 158756
  | 92 => 158757
  | 93 => 159782
  | 94 => 159785
  | 95 => 159786
  | 96 => 160125
  | 97 => 160128
  | 98 => 160129
  | 99 => 161154
  | 100 => 161157
  | 101 => 161158
  | 102 => 162183
  | 103 => 162186
  | 104 => 162187
  | 105 => 162526
  | 106 => 162529
  | 107 => 162530
  | 108 => 252434
  | 109 => 252437
  | 110 => 252438
  | 111 => 253463
  | 112 => 253466
  | 113 => 253467
  | 114 => 253806
  | 115 => 253809
  | 116 => 253810
  | 117 => 259637
  | 118 => 259640
  | 119 => 259641
  | 120 => 260666
  | 121 => 260669
  | 122 => 260670
  | 123 => 261009
  | 124 => 261012
  | 125 => 261013
  | 126 => 262038
  | 127 => 262041
  | 128 => 262042
  | 129 => 263067
  | 130 => 263070
  | 131 => 263071
  | 132 => 263410
  | 133 => 263413
  | 134 => 263414
  | 135 => 403368
  | 136 => 403371
  | 137 => 403372
  | 138 => 403536
  | 139 => 403539
  | 140 => 403540
  | 141 => 403592
  | 142 => 403595
  | 143 => 403596
  | 144 => 404397
  | 145 => 404400
  | 146 => 404401
  | 147 => 404565
  | 148 => 404568
  | 149 => 404569
  | 150 => 404621
  | 151 => 404624
  | 152 => 404625
  | 153 => 404740
  | 154 => 404743
  | 155 => 404744
  | 156 => 404908
  | 157 => 404911
  | 158 => 404912
  | 159 => 404964
  | 160 => 404967
  | 161 => 404968
  | 162 => 410571
  | 163 => 410574
  | 164 => 410575
  | 165 => 410739
  | 166 => 410742
  | 167 => 410743
  | 168 => 410795
  | 169 => 410798
  | 170 => 410799
  | 171 => 411600
  | 172 => 411603
  | 173 => 411604
  | 174 => 411768
  | 175 => 411771
  | 176 => 411772
  | 177 => 411824
  | 178 => 411827
  | 179 => 411828
  | 180 => 411943
  | 181 => 411946
  | 182 => 411947
  | 183 => 412111
  | 184 => 412114
  | 185 => 412115
  | 186 => 412167
  | 187 => 412170
  | 188 => 412171
  | 189 => 412972
  | 190 => 412975
  | 191 => 412976
  | 192 => 413140
  | 193 => 413143
  | 194 => 413144
  | 195 => 413196
  | 196 => 413199
  | 197 => 413200
  | 198 => 414001
  | 199 => 414004
  | 200 => 414005
  | 201 => 414169
  | 202 => 414172
  | 203 => 414173
  | 204 => 414225
  | 205 => 414228
  | 206 => 414229
  | 207 => 414344
  | 208 => 414347
  | 209 => 414348
  | 210 => 414512
  | 211 => 414515
  | 212 => 414516
  | 213 => 414568
  | 214 => 414571
  | 215 => 414572
  | 216 => 537824
  | 217 => 537827
  | 218 => 537828
  | 219 => 537992
  | 220 => 537995
  | 221 => 537996
  | 222 => 538048
  | 223 => 538051
  | 224 => 538052
  | 225 => 538853
  | 226 => 538856
  | 227 => 538857
  | 228 => 539021
  | 229 => 539024
  | 230 => 539025
  | 231 => 539077
  | 232 => 539080
  | 233 => 539081
  | 234 => 539196
  | 235 => 539199
  | 236 => 539200
  | 237 => 539364
  | 238 => 539367
  | 239 => 539368
  | 240 => 539420
  | 241 => 539423
  | 242 => 539424
  | 243 => 545027
  | 244 => 545030
  | 245 => 545031
  | 246 => 545195
  | 247 => 545198
  | 248 => 545199
  | 249 => 545251
  | 250 => 545254
  | 251 => 545255
  | 252 => 546056
  | 253 => 546059
  | 254 => 546060
  | 255 => 546224
  | 256 => 546227
  | 257 => 546228
  | 258 => 546280
  | 259 => 546283
  | 260 => 546284
  | 261 => 546399
  | 262 => 546402
  | 263 => 546403
  | 264 => 546567
  | 265 => 546570
  | 266 => 546571
  | 267 => 546623
  | 268 => 546626
  | 269 => 546627
  | 270 => 547428
  | 271 => 547431
  | 272 => 547432
  | 273 => 547596
  | 274 => 547599
  | 275 => 547600
  | 276 => 547652
  | 277 => 547655
  | 278 => 547656
  | 279 => 548457
  | 280 => 548460
  | 281 => 548461
  | 282 => 548625
  | 283 => 548628
  | 284 => 548629
  | 285 => 548681
  | 286 => 548684
  | 287 => 548685
  | 288 => 548800
  | 289 => 548803
  | 290 => 548804
  | 291 => 548968
  | 292 => 548971
  | 293 => 548972
  | 294 => 549024
  | 295 => 549027
  | 296 => 549028
  | 297 => 689150
  | 298 => 689153
  | 299 => 689154
  | 300 => 690179
  | 301 => 690182
  | 302 => 690183
  | 303 => 690522
  | 304 => 690525
  | 305 => 690526
  | 306 => 696353
  | 307 => 696356
  | 308 => 696357
  | 309 => 697382
  | 310 => 697385
  | 311 => 697386
  | 312 => 697725
  | 313 => 697728
  | 314 => 697729
  | 315 => 698754
  | 316 => 698757
  | 317 => 698758
  | 318 => 699783
  | 319 => 699786
  | 320 => 699787
  | 321 => 700126
  | 322 => 700129
  | 323 => 700130
  | 324 => 790034
  | 325 => 790037
  | 326 => 790038
  | 327 => 791063
  | 328 => 791066
  | 329 => 791067
  | 330 => 791406
  | 331 => 791409
  | 332 => 791410
  | 333 => 797237
  | 334 => 797240
  | 335 => 797241
  | 336 => 798266
  | 337 => 798269
  | 338 => 798270
  | 339 => 798609
  | 340 => 798612
  | 341 => 798613
  | 342 => 799638
  | 343 => 799641
  | 344 => 799642
  | 345 => 800667
  | 346 => 800670
  | 347 => 800671
  | 348 => 801010
  | 349 => 801013
  | _ => 801014

def endE7D (j : Fin 351) : Fin 7 → Fin 7 := allMaps7 (eidx7D j)

/-- Indices of the other `823192`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset7D : Array Nat := #[
  0, 3, 4, 168, 171, 172, 224, 227, 228, 1029, 1032, 1033, 1197, 1200, 1201, 1253, 1256, 1257,
  1372, 1375, 1376, 1540, 1543, 1544, 1596, 1599, 1600, 7203, 7206, 7207, 7371, 7374, 7375, 7427,
  7430, 7431, 8232, 8235, 8236, 8400, 8403, 8404, 8456, 8459, 8460, 8575, 8578, 8579, 8743, 8746,
  8747, 8799, 8802, 8803, 9604, 9607, 9608, 9772, 9775, 9776, 9828, 9831, 9832, 10633, 10636,
  10637, 10801, 10804, 10805, 10857, 10860, 10861, 10976, 10979, 10980, 11144, 11147, 11148,
  11200, 11203, 11204, 151550, 151553, 151554, 152579, 152582, 152583, 152922, 152925, 152926,
  158753, 158756, 158757, 159782, 159785, 159786, 160125, 160128, 160129, 161154, 161157, 161158,
  162183, 162186, 162187, 162526, 162529, 162530, 252434, 252437, 252438, 253463, 253466, 253467,
  253806, 253809, 253810, 259637, 259640, 259641, 260666, 260669, 260670, 261009, 261012, 261013,
  262038, 262041, 262042, 263067, 263070, 263071, 263410, 263413, 263414, 403368, 403371, 403372,
  403536, 403539, 403540, 403592, 403595, 403596, 404397, 404400, 404401, 404565, 404568, 404569,
  404621, 404624, 404625, 404740, 404743, 404744, 404908, 404911, 404912, 404964, 404967, 404968,
  410571, 410574, 410575, 410739, 410742, 410743, 410795, 410798, 410799, 411600, 411603, 411604,
  411768, 411771, 411772, 411824, 411827, 411828, 411943, 411946, 411947, 412111, 412114, 412115,
  412167, 412170, 412171, 412972, 412975, 412976, 413140, 413143, 413144, 413196, 413199, 413200,
  414001, 414004, 414005, 414169, 414172, 414173, 414225, 414228, 414229, 414344, 414347, 414348,
  414512, 414515, 414516, 414568, 414571, 414572, 537824, 537827, 537828, 537992, 537995, 537996,
  538048, 538051, 538052, 538853, 538856, 538857, 539021, 539024, 539025, 539077, 539080, 539081,
  539196, 539199, 539200, 539364, 539367, 539368, 539420, 539423, 539424, 545027, 545030, 545031,
  545195, 545198, 545199, 545251, 545254, 545255, 546056, 546059, 546060, 546224, 546227, 546228,
  546280, 546283, 546284, 546399, 546402, 546403, 546567, 546570, 546571, 546623, 546626, 546627,
  547428, 547431, 547432, 547596, 547599, 547600, 547652, 547655, 547656, 548457, 548460, 548461,
  548625, 548628, 548629, 548681, 548684, 548685, 548800, 548803, 548804, 548968, 548971, 548972,
  549024, 549027, 549028, 689150, 689153, 689154, 690179, 690182, 690183, 690522, 690525, 690526,
  696353, 696356, 696357, 697382, 697385, 697386, 697725, 697728, 697729, 698754, 698757, 698758,
  699783, 699786, 699787, 700126, 700129, 700130, 790034, 790037, 790038, 791063, 791066, 791067,
  791406, 791409, 791410, 797237, 797240, 797241, 798266, 798269, 798270, 798609, 798612, 798613,
  799638, 799641, 799642, 800667, 800670, 800671, 801010, 801013, 801014]

def xarr7D : Array Nat := Id.run do
  let mut out := Array.mkEmpty 823192
  let mut k := 0
  for i in [0:823543] do
    if k < eset7D.size && eset7D[k]! == i then
      k := k + 1
    else
      out := out.push i
  return out

def xidx7D (j : Fin 823192) : Fin 823543 :=
  ⟨min (xarr7D.getD j.1 0) 823542, by omega⟩

def endX7D (j : Fin 823192) : Fin 7 → Fin 7 := allMaps7 (xidx7D j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end7D` is given. -/
def uidx7D : Fin 12 → Fin 351
  | 0 => 345
  | 1 => 312
  | 2 => 123
  | 3 => 102
  | 4 => 331
  | 5 => 316
  | 6 => 127
  | 7 => 88
  | 8 => 335
  | 9 => 302
  | 10 => 113
  | 11 => 92

theorem permE7D_eq_endE7D (i : Fin 12) : permE7D i = endE7D (uidx7D i) := by
  revert i; decide

/-- One representative per orbit of the group on the `49` cells; there are `8`, so an invariant
operation is `8` values. -/
def rep7D : Fin 8 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)
  | 6 => (1, 5)
  | 7 => (1, 6)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr7D : Fin 7 → Fin 7 → Fin 8 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (2, 1)
  | 0, 5 => (1, 2)
  | 0, 6 => (1, 3)
  | 1, 0 => (3, 0)
  | 1, 1 => (4, 0)
  | 1, 2 => (5, 0)
  | 1, 3 => (3, 4)
  | 1, 4 => (3, 8)
  | 1, 5 => (6, 0)
  | 1, 6 => (7, 0)
  | 2, 0 => (3, 1)
  | 2, 1 => (5, 1)
  | 2, 2 => (4, 1)
  | 2, 3 => (3, 5)
  | 2, 4 => (3, 9)
  | 2, 5 => (7, 1)
  | 2, 6 => (6, 1)
  | 3, 0 => (2, 5)
  | 3, 1 => (1, 4)
  | 3, 2 => (1, 5)
  | 3, 3 => (0, 4)
  | 3, 4 => (2, 4)
  | 3, 5 => (1, 6)
  | 3, 6 => (1, 7)
  | 4, 0 => (2, 8)
  | 4, 1 => (1, 8)
  | 4, 2 => (1, 9)
  | 4, 3 => (2, 9)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 10)
  | 4, 6 => (1, 11)
  | 5, 0 => (3, 2)
  | 5, 1 => (6, 2)
  | 5, 2 => (7, 2)
  | 5, 3 => (3, 6)
  | 5, 4 => (3, 10)
  | 5, 5 => (4, 2)
  | 5, 6 => (5, 2)
  | 6, 0 => (3, 3)
  | 6, 1 => (7, 3)
  | 6, 2 => (6, 3)
  | 6, 3 => (3, 7)
  | 6, 4 => (3, 11)
  | 6, 5 => (5, 3)
  | 6, 6 => (4, 3)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx7D0 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val7D0 : Fin 1 → Fin 7
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdx7D1 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, `4`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx7D2 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 3
def val7D2 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 3
  | 2 => 4

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdx7D3 : Fin 1 → Fin 12
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `1`, `2`, `5`, `6`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx7D4 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 4
  | 2 => 8
def val7D4 : Fin 4 → Fin 7
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 6

/-- The `3` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `1`, `2`, `5`, `6`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx7D5 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 4
  | 2 => 8
def val7D5 : Fin 4 → Fin 7
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 6

/-- The `3` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `1`, `2`, `5`, `6`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx7D6 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 4
  | 2 => 8
def val7D6 : Fin 4 → Fin 7
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 6

/-- The `3` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `1`, `2`, `5`, `6`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx7D7 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 4
  | 2 => 8
def val7D7 : Fin 4 → Fin 7
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 6

/-- The `8` orbit values named by the family's arguments. -/
def dec7D (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4) : Fin 8 → Fin 7
  | 0 => val7D0 a
  | 1 => b
  | 2 => val7D2 c
  | 3 => d
  | 4 => val7D4 e
  | 5 => val7D5 f
  | 6 => val7D6 g
  | 7 => val7D7 h

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab7D_eq_transport`). -/
def tab7D (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => val7D0 a
  | 0, 1 => b
  | 0, 2 => pE7D1 b
  | 0, 3 => val7D2 c
  | 0, 4 => pE7D1 (val7D2 c)
  | 0, 5 => pE7D2 b
  | 0, 6 => pE7D3 b
  | 1, 0 => d
  | 1, 1 => val7D4 e
  | 1, 2 => val7D5 f
  | 1, 3 => pE7D4 d
  | 1, 4 => pE7D8 d
  | 1, 5 => val7D6 g
  | 1, 6 => val7D7 h
  | 2, 0 => pE7D1 d
  | 2, 1 => pE7D1 (val7D5 f)
  | 2, 2 => pE7D1 (val7D4 e)
  | 2, 3 => pE7D5 d
  | 2, 4 => pE7D9 d
  | 2, 5 => pE7D1 (val7D7 h)
  | 2, 6 => pE7D1 (val7D6 g)
  | 3, 0 => pE7D5 (val7D2 c)
  | 3, 1 => pE7D4 b
  | 3, 2 => pE7D5 b
  | 3, 3 => pE7D4 (val7D0 a)
  | 3, 4 => pE7D4 (val7D2 c)
  | 3, 5 => pE7D6 b
  | 3, 6 => pE7D7 b
  | 4, 0 => pE7D8 (val7D2 c)
  | 4, 1 => pE7D8 b
  | 4, 2 => pE7D9 b
  | 4, 3 => pE7D9 (val7D2 c)
  | 4, 4 => pE7D8 (val7D0 a)
  | 4, 5 => pE7D10 b
  | 4, 6 => pE7D11 b
  | 5, 0 => pE7D2 d
  | 5, 1 => pE7D2 (val7D6 g)
  | 5, 2 => pE7D2 (val7D7 h)
  | 5, 3 => pE7D6 d
  | 5, 4 => pE7D10 d
  | 5, 5 => pE7D2 (val7D4 e)
  | 5, 6 => pE7D2 (val7D5 f)
  | 6, 0 => pE7D3 d
  | 6, 1 => pE7D3 (val7D7 h)
  | 6, 2 => pE7D3 (val7D6 g)
  | 6, 3 => pE7D7 d
  | 6, 4 => pE7D11 d
  | 6, 5 => pE7D3 (val7D5 f)
  | 6, 6 => pE7D3 (val7D4 e)

theorem tab7D_eq_transport (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4) :
    tab7D a b c d e f g h = Magma.transport permE7D tr7D (dec7D a b c d e f g h) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `8` magmas on `Fin 7` whose endomorphism monoid is exactly this one, listed under one index.
Of the `37632` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem7D : Fin 8 → Fin 7 → Fin 7 → Fin 7
  | 0 => tab7D 0 0 0 1 1 1 0 1
  | 1 => tab7D 0 0 0 1 1 1 1 0
  | 2 => tab7D 0 0 0 2 1 1 0 1
  | 3 => tab7D 0 0 0 2 1 1 1 0
  | 4 => tab7D 0 1 1 0 1 0 2 2
  | 5 => tab7D 0 1 1 0 1 0 3 3
  | 6 => tab7D 0 2 1 0 1 0 2 2
  | 7 => tab7D 0 2 1 0 1 0 3 3

/-- The arguments as one mixed-radix index, which is how `rankIdx7D` is addressed. -/
def encT7D (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4) : Nat :=
  a.1 * 37632 +
    b.1 * 5376 +
    c.1 * 1792 +
    d.1 * 256 +
    e.1 * 64 +
    f.1 * 16 +
    g.1 * 4 +
    h.1

/-- Which of the `8` members a given invariant tuple is, so that `mem_of_isExact7D` can name one
rather than search the list for it. The `37624` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank7D` excludes them. Read only by `native_decide`. -/
def rankIdx7D : Nat → Nat
  | 337 => 0
  | 340 => 1
  | 593 => 2
  | 596 => 3
  | 7242 => 4
  | 7247 => 5
  | 12618 => 6
  | 12623 => 7
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank7D (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4) : Fin 8 :=
  ⟨min (rankIdx7D (encT7D a b c d e f g h)) 7, by omega⟩


/-- `1` of the `351` demanded maps and `4` of the `823192` forbidden ones, enough to separate the
`8` members from the other `37624` invariant tuples between them. The certificate demands all `351`
-- the group has to be among them -- but forbids only these: `mem_rank7D` scans them once per tuple
with a scan quadratic in their length, and nothing else reads the forbidden side. -/
def e0idx7D : Fin 1 → Fin 351
  | 0 => 4
def x0idx7D : Fin 4 → Fin 823192
  | 0 => 137176
  | 1 => 151245
  | 2 => 151287
  | 3 => 151508

def endE07D (j : Fin 1) : Fin 7 → Fin 7 := endE7D (e0idx7D j)

def endX07D (j : Fin 4) : Fin 7 → Fin 7 := endX7D (x0idx7D j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end7D (i : Fin 8) : Magma (Fin 7) := Magma.mk (mem7D i)

theorem end7D_isEndo (i : Fin 8) (j : Fin 351) : (end7D i).IsEndo (endE7D j) := by
  revert i j; native_decide

theorem end7D_not_isEndo (i : Fin 8) (j : Fin 4) : ¬ (end7D i).IsEndo (endX07D j) := by
  revert i j; native_decide

/-- `rank7D` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem7D` for the index would be a comparison per tuple and
member. -/
theorem mem_rank7D (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4)
    (hx : Magma.isExact (tab7D a b c d e f g h) endE07D endX07D = true) :
    mem7D (rank7D a b c d e f g h) = tab7D a b c d e f g h := by
  revert hx; revert a b c d e f g h; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `8` listed
members. -/
theorem mem_of_isExact7D (a : Fin 1) (b : Fin 7) (c : Fin 3) (d : Fin 7) (e f g h : Fin 4)
    (hx : Magma.isExact (tab7D a b c d e f g h) endE07D endX07D = true) :
    ∃ idx, mem7D idx = tab7D a b c d e f g h :=
  ⟨_, mem_rank7D a b c d e f g h hx⟩

/-- A magma on `Fin 7` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end7D`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact7D` turns that into a member index. -/
theorem exists_end7D {M : Magma (Fin 7)} (hE : ∀ j, M.IsEndo (endE7D j))
    (hX : ∀ j, ¬ M.IsEndo (endX07D j)) : ∃ i, end7D i = M := by
  have hP : ∀ i, M.IsEndo (permE7D i) := by
    intro i; rw [permE7D_eq_endE7D]; exact hE (uidx7D i)
  have hop : M.op = Magma.transport permE7D tr7D (fun i ↦ M.op (rep7D i).1 (rep7D i).2) :=
    Magma.op_eq_transport (rep := rep7D) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D0) (a := (rep7D 0).1) (b := (rep7D 0).2)
    (val := val7D0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D1) (a := (rep7D 1).1) (b := (rep7D 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D2) (a := (rep7D 2).1) (b := (rep7D 2).2)
    (val := val7D2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D3) (a := (rep7D 3).1) (b := (rep7D 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D4) (a := (rep7D 4).1) (b := (rep7D 4).2)
    (val := val7D4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D5) (a := (rep7D 5).1) (b := (rep7D 5).2)
    (val := val7D5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D6) (a := (rep7D 6).1) (b := (rep7D 6).2)
    (val := val7D6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE7D) (idx := stabIdx7D7) (a := (rep7D 7).1) (b := (rep7D 7).2)
    (val := val7D7) hP (by decide) (by decide)
  have hdec : dec7D a b c d e f g h = fun i ↦ M.op (rep7D i).1 (rep7D i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
  have key : tab7D a b c d e f g h = M.op := by
    rw [tab7D_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab7D a b c d e f g h) endE07D endX07D = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx7D j), hX⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact7D a b c d e f g h hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose endomorphism
monoid is exactly the order-`351` monoid of `Magma.endE7D`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end7D {L L' : Law.NatMagmaLaw} {i : Fin 8}
    (hsrc : @satisfies _ (Fin 7) (Magma.end7D i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.end7D j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end7D i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end7D
    (fun k ↦ (Magma.end7D_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end7D_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
