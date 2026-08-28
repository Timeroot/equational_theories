import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `N` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `384` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6N0 : Fin 6 → Fin 6 := id
def pE6N1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6N2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6N3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6N4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6N5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6N6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6N7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6N8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6N9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6N10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6N11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6N : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6N0
  | 1 => pE6N1
  | 2 => pE6N2
  | 3 => pE6N3
  | 4 => pE6N4
  | 5 => pE6N5
  | 6 => pE6N6
  | 7 => pE6N7
  | 8 => pE6N8
  | 9 => pE6N9
  | 10 => pE6N10
  | 11 => pE6N11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `384` self-maps that must be endomorphisms: `102222`, `012222`, `222222`,
`333222`, `444222`, `555222`, `102322`, `012322`, `222322`, `333322`, `444322`, `555322`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6N : Fin 384 → Fin 46656
  | 0 => 18649
  | 1 => 18654
  | 2 => 18662
  | 3 => 18705
  | 4 => 18748
  | 5 => 18791
  | 6 => 18865
  | 7 => 18870
  | 8 => 18878
  | 9 => 18921
  | 10 => 18964
  | 11 => 19007
  | 12 => 19081
  | 13 => 19086
  | 14 => 19094
  | 15 => 19137
  | 16 => 19180
  | 17 => 19223
  | 18 => 19297
  | 19 => 19302
  | 20 => 19310
  | 21 => 19353
  | 22 => 19396
  | 23 => 19439
  | 24 => 19945
  | 25 => 19950
  | 26 => 19958
  | 27 => 20001
  | 28 => 20044
  | 29 => 20087
  | 30 => 20161
  | 31 => 20166
  | 32 => 20174
  | 33 => 20217
  | 34 => 20260
  | 35 => 20303
  | 36 => 20377
  | 37 => 20382
  | 38 => 20390
  | 39 => 20433
  | 40 => 20476
  | 41 => 20519
  | 42 => 20593
  | 43 => 20598
  | 44 => 20606
  | 45 => 20649
  | 46 => 20692
  | 47 => 20735
  | 48 => 21241
  | 49 => 21246
  | 50 => 21254
  | 51 => 21297
  | 52 => 21340
  | 53 => 21383
  | 54 => 21457
  | 55 => 21462
  | 56 => 21470
  | 57 => 21513
  | 58 => 21556
  | 59 => 21599
  | 60 => 21673
  | 61 => 21678
  | 62 => 21686
  | 63 => 21729
  | 64 => 21772
  | 65 => 21815
  | 66 => 21889
  | 67 => 21894
  | 68 => 21902
  | 69 => 21945
  | 70 => 21988
  | 71 => 22031
  | 72 => 22537
  | 73 => 22542
  | 74 => 22550
  | 75 => 22593
  | 76 => 22636
  | 77 => 22679
  | 78 => 22753
  | 79 => 22758
  | 80 => 22766
  | 81 => 22809
  | 82 => 22852
  | 83 => 22895
  | 84 => 22969
  | 85 => 22974
  | 86 => 22982
  | 87 => 23025
  | 88 => 23068
  | 89 => 23111
  | 90 => 23185
  | 91 => 23190
  | 92 => 23198
  | 93 => 23241
  | 94 => 23284
  | 95 => 23327
  | 96 => 26425
  | 97 => 26430
  | 98 => 26438
  | 99 => 26481
  | 100 => 26524
  | 101 => 26567
  | 102 => 26641
  | 103 => 26646
  | 104 => 26654
  | 105 => 26697
  | 106 => 26740
  | 107 => 26783
  | 108 => 26857
  | 109 => 26862
  | 110 => 26870
  | 111 => 26913
  | 112 => 26956
  | 113 => 26999
  | 114 => 27073
  | 115 => 27078
  | 116 => 27086
  | 117 => 27129
  | 118 => 27172
  | 119 => 27215
  | 120 => 27721
  | 121 => 27726
  | 122 => 27734
  | 123 => 27777
  | 124 => 27820
  | 125 => 27863
  | 126 => 27937
  | 127 => 27942
  | 128 => 27950
  | 129 => 27993
  | 130 => 28036
  | 131 => 28079
  | 132 => 28153
  | 133 => 28158
  | 134 => 28166
  | 135 => 28209
  | 136 => 28252
  | 137 => 28295
  | 138 => 28369
  | 139 => 28374
  | 140 => 28382
  | 141 => 28425
  | 142 => 28468
  | 143 => 28511
  | 144 => 29017
  | 145 => 29022
  | 146 => 29030
  | 147 => 29073
  | 148 => 29116
  | 149 => 29159
  | 150 => 29233
  | 151 => 29238
  | 152 => 29246
  | 153 => 29289
  | 154 => 29332
  | 155 => 29375
  | 156 => 29449
  | 157 => 29454
  | 158 => 29462
  | 159 => 29505
  | 160 => 29548
  | 161 => 29591
  | 162 => 29665
  | 163 => 29670
  | 164 => 29678
  | 165 => 29721
  | 166 => 29764
  | 167 => 29807
  | 168 => 30313
  | 169 => 30318
  | 170 => 30326
  | 171 => 30369
  | 172 => 30412
  | 173 => 30455
  | 174 => 30529
  | 175 => 30534
  | 176 => 30542
  | 177 => 30585
  | 178 => 30628
  | 179 => 30671
  | 180 => 30745
  | 181 => 30750
  | 182 => 30758
  | 183 => 30801
  | 184 => 30844
  | 185 => 30887
  | 186 => 30961
  | 187 => 30966
  | 188 => 30974
  | 189 => 31017
  | 190 => 31060
  | 191 => 31103
  | 192 => 34201
  | 193 => 34206
  | 194 => 34214
  | 195 => 34257
  | 196 => 34300
  | 197 => 34343
  | 198 => 34417
  | 199 => 34422
  | 200 => 34430
  | 201 => 34473
  | 202 => 34516
  | 203 => 34559
  | 204 => 34633
  | 205 => 34638
  | 206 => 34646
  | 207 => 34689
  | 208 => 34732
  | 209 => 34775
  | 210 => 34849
  | 211 => 34854
  | 212 => 34862
  | 213 => 34905
  | 214 => 34948
  | 215 => 34991
  | 216 => 35497
  | 217 => 35502
  | 218 => 35510
  | 219 => 35553
  | 220 => 35596
  | 221 => 35639
  | 222 => 35713
  | 223 => 35718
  | 224 => 35726
  | 225 => 35769
  | 226 => 35812
  | 227 => 35855
  | 228 => 35929
  | 229 => 35934
  | 230 => 35942
  | 231 => 35985
  | 232 => 36028
  | 233 => 36071
  | 234 => 36145
  | 235 => 36150
  | 236 => 36158
  | 237 => 36201
  | 238 => 36244
  | 239 => 36287
  | 240 => 36793
  | 241 => 36798
  | 242 => 36806
  | 243 => 36849
  | 244 => 36892
  | 245 => 36935
  | 246 => 37009
  | 247 => 37014
  | 248 => 37022
  | 249 => 37065
  | 250 => 37108
  | 251 => 37151
  | 252 => 37225
  | 253 => 37230
  | 254 => 37238
  | 255 => 37281
  | 256 => 37324
  | 257 => 37367
  | 258 => 37441
  | 259 => 37446
  | 260 => 37454
  | 261 => 37497
  | 262 => 37540
  | 263 => 37583
  | 264 => 38089
  | 265 => 38094
  | 266 => 38102
  | 267 => 38145
  | 268 => 38188
  | 269 => 38231
  | 270 => 38305
  | 271 => 38310
  | 272 => 38318
  | 273 => 38361
  | 274 => 38404
  | 275 => 38447
  | 276 => 38521
  | 277 => 38526
  | 278 => 38534
  | 279 => 38577
  | 280 => 38620
  | 281 => 38663
  | 282 => 38737
  | 283 => 38742
  | 284 => 38750
  | 285 => 38793
  | 286 => 38836
  | 287 => 38879
  | 288 => 41977
  | 289 => 41982
  | 290 => 41990
  | 291 => 42033
  | 292 => 42076
  | 293 => 42119
  | 294 => 42193
  | 295 => 42198
  | 296 => 42206
  | 297 => 42249
  | 298 => 42292
  | 299 => 42335
  | 300 => 42409
  | 301 => 42414
  | 302 => 42422
  | 303 => 42465
  | 304 => 42508
  | 305 => 42551
  | 306 => 42625
  | 307 => 42630
  | 308 => 42638
  | 309 => 42681
  | 310 => 42724
  | 311 => 42767
  | 312 => 43273
  | 313 => 43278
  | 314 => 43286
  | 315 => 43329
  | 316 => 43372
  | 317 => 43415
  | 318 => 43489
  | 319 => 43494
  | 320 => 43502
  | 321 => 43545
  | 322 => 43588
  | 323 => 43631
  | 324 => 43705
  | 325 => 43710
  | 326 => 43718
  | 327 => 43761
  | 328 => 43804
  | 329 => 43847
  | 330 => 43921
  | 331 => 43926
  | 332 => 43934
  | 333 => 43977
  | 334 => 44020
  | 335 => 44063
  | 336 => 44569
  | 337 => 44574
  | 338 => 44582
  | 339 => 44625
  | 340 => 44668
  | 341 => 44711
  | 342 => 44785
  | 343 => 44790
  | 344 => 44798
  | 345 => 44841
  | 346 => 44884
  | 347 => 44927
  | 348 => 45001
  | 349 => 45006
  | 350 => 45014
  | 351 => 45057
  | 352 => 45100
  | 353 => 45143
  | 354 => 45217
  | 355 => 45222
  | 356 => 45230
  | 357 => 45273
  | 358 => 45316
  | 359 => 45359
  | 360 => 45865
  | 361 => 45870
  | 362 => 45878
  | 363 => 45921
  | 364 => 45964
  | 365 => 46007
  | 366 => 46081
  | 367 => 46086
  | 368 => 46094
  | 369 => 46137
  | 370 => 46180
  | 371 => 46223
  | 372 => 46297
  | 373 => 46302
  | 374 => 46310
  | 375 => 46353
  | 376 => 46396
  | 377 => 46439
  | 378 => 46513
  | 379 => 46518
  | 380 => 46526
  | 381 => 46569
  | 382 => 46612
  | _ => 46655

def endE6N (j : Fin 384) : Fin 6 → Fin 6 := allMaps6 (eidx6N j)

/-- Indices of the other `46272`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6N : Array Nat := #[
  18649, 18654, 18662, 18705, 18748, 18791, 18865, 18870, 18878, 18921, 18964, 19007, 19081,
  19086, 19094, 19137, 19180, 19223, 19297, 19302, 19310, 19353, 19396, 19439, 19945, 19950,
  19958, 20001, 20044, 20087, 20161, 20166, 20174, 20217, 20260, 20303, 20377, 20382, 20390,
  20433, 20476, 20519, 20593, 20598, 20606, 20649, 20692, 20735, 21241, 21246, 21254, 21297,
  21340, 21383, 21457, 21462, 21470, 21513, 21556, 21599, 21673, 21678, 21686, 21729, 21772,
  21815, 21889, 21894, 21902, 21945, 21988, 22031, 22537, 22542, 22550, 22593, 22636, 22679,
  22753, 22758, 22766, 22809, 22852, 22895, 22969, 22974, 22982, 23025, 23068, 23111, 23185,
  23190, 23198, 23241, 23284, 23327, 26425, 26430, 26438, 26481, 26524, 26567, 26641, 26646,
  26654, 26697, 26740, 26783, 26857, 26862, 26870, 26913, 26956, 26999, 27073, 27078, 27086,
  27129, 27172, 27215, 27721, 27726, 27734, 27777, 27820, 27863, 27937, 27942, 27950, 27993,
  28036, 28079, 28153, 28158, 28166, 28209, 28252, 28295, 28369, 28374, 28382, 28425, 28468,
  28511, 29017, 29022, 29030, 29073, 29116, 29159, 29233, 29238, 29246, 29289, 29332, 29375,
  29449, 29454, 29462, 29505, 29548, 29591, 29665, 29670, 29678, 29721, 29764, 29807, 30313,
  30318, 30326, 30369, 30412, 30455, 30529, 30534, 30542, 30585, 30628, 30671, 30745, 30750,
  30758, 30801, 30844, 30887, 30961, 30966, 30974, 31017, 31060, 31103, 34201, 34206, 34214,
  34257, 34300, 34343, 34417, 34422, 34430, 34473, 34516, 34559, 34633, 34638, 34646, 34689,
  34732, 34775, 34849, 34854, 34862, 34905, 34948, 34991, 35497, 35502, 35510, 35553, 35596,
  35639, 35713, 35718, 35726, 35769, 35812, 35855, 35929, 35934, 35942, 35985, 36028, 36071,
  36145, 36150, 36158, 36201, 36244, 36287, 36793, 36798, 36806, 36849, 36892, 36935, 37009,
  37014, 37022, 37065, 37108, 37151, 37225, 37230, 37238, 37281, 37324, 37367, 37441, 37446,
  37454, 37497, 37540, 37583, 38089, 38094, 38102, 38145, 38188, 38231, 38305, 38310, 38318,
  38361, 38404, 38447, 38521, 38526, 38534, 38577, 38620, 38663, 38737, 38742, 38750, 38793,
  38836, 38879, 41977, 41982, 41990, 42033, 42076, 42119, 42193, 42198, 42206, 42249, 42292,
  42335, 42409, 42414, 42422, 42465, 42508, 42551, 42625, 42630, 42638, 42681, 42724, 42767,
  43273, 43278, 43286, 43329, 43372, 43415, 43489, 43494, 43502, 43545, 43588, 43631, 43705,
  43710, 43718, 43761, 43804, 43847, 43921, 43926, 43934, 43977, 44020, 44063, 44569, 44574,
  44582, 44625, 44668, 44711, 44785, 44790, 44798, 44841, 44884, 44927, 45001, 45006, 45014,
  45057, 45100, 45143, 45217, 45222, 45230, 45273, 45316, 45359, 45865, 45870, 45878, 45921,
  45964, 46007, 46081, 46086, 46094, 46137, 46180, 46223, 46297, 46302, 46310, 46353, 46396,
  46439, 46513, 46518, 46526, 46569, 46612, 46655]

def xarr6N : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6N.contains i)

def xidx6N (j : Fin 46272) : Fin 46656 :=
  ⟨min (xarr6N.getD j.1 0) 46655, by omega⟩

def endX6N (j : Fin 46272) : Fin 6 → Fin 6 := allMaps6 (xidx6N j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6N` is given. -/
def uidx6N : Fin 12 → Fin 384
  | 0 => 343
  | 1 => 271
  | 2 => 325
  | 3 => 181
  | 4 => 235
  | 5 => 163
  | 6 => 342
  | 7 => 270
  | 8 => 324
  | 9 => 180
  | 10 => 234
  | 11 => 162

theorem permE6N_eq_endE6N (i : Fin 12) : permE6N i = endE6N (uidx6N i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6N : Fin 11 → Fin 6 × Fin 6
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
def tr6N : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6N0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6N0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6N1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6N1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6N2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6N2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6N3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6N3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6N4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6N4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6N5 : Fin 12 → Fin 12
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
def val6N5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6N6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6N6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6N7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6N7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6N8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6N8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6N9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6N9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6N10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6N10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6N (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6N0 a
  | 1 => val6N1 b
  | 2 => val6N2 c
  | 3 => val6N3 d
  | 4 => val6N4 e
  | 5 => val6N5 f
  | 6 => val6N6 g
  | 7 => val6N7 h
  | 8 => val6N8 i
  | 9 => val6N9 j
  | 10 => val6N10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6N_eq_transport`). -/
def tab6N (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6N0 a
  | 0, 1 => val6N1 b
  | 0, 2 => val6N2 c
  | 0, 3 => val6N3 d
  | 0, 4 => pE6N2 (val6N3 d)
  | 0, 5 => pE6N4 (val6N3 d)
  | 1, 0 => pE6N6 (val6N1 b)
  | 1, 1 => pE6N6 (val6N0 a)
  | 1, 2 => pE6N6 (val6N2 c)
  | 1, 3 => pE6N6 (val6N3 d)
  | 1, 4 => pE6N8 (val6N3 d)
  | 1, 5 => pE6N10 (val6N3 d)
  | 2, 0 => val6N4 e
  | 2, 1 => pE6N6 (val6N4 e)
  | 2, 2 => val6N5 f
  | 2, 3 => val6N6 g
  | 2, 4 => pE6N2 (val6N6 g)
  | 2, 5 => pE6N4 (val6N6 g)
  | 3, 0 => val6N7 h
  | 3, 1 => pE6N6 (val6N7 h)
  | 3, 2 => val6N8 i
  | 3, 3 => val6N9 j
  | 3, 4 => val6N10 k
  | 3, 5 => pE6N1 (val6N10 k)
  | 4, 0 => pE6N2 (val6N7 h)
  | 4, 1 => pE6N8 (val6N7 h)
  | 4, 2 => pE6N2 (val6N8 i)
  | 4, 3 => pE6N2 (val6N10 k)
  | 4, 4 => pE6N2 (val6N9 j)
  | 4, 5 => pE6N3 (val6N10 k)
  | 5, 0 => pE6N4 (val6N7 h)
  | 5, 1 => pE6N10 (val6N7 h)
  | 5, 2 => pE6N4 (val6N8 i)
  | 5, 3 => pE6N4 (val6N10 k)
  | 5, 4 => pE6N5 (val6N10 k)
  | 5, 5 => pE6N4 (val6N9 j)

theorem tab6N_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6N a b c d e f g h i j k = Magma.transport permE6N tr6N (dec6N a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `22` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6N : Fin 22 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6N 1 0 2 2 2 0 0 3 1 1 1
  | 1 => tab6N 1 0 2 3 2 0 1 2 0 1 2
  | 2 => tab6N 1 1 2 2 2 0 0 3 1 1 1
  | 3 => tab6N 1 1 2 3 2 0 1 2 0 1 2
  | 4 => tab6N 1 2 0 0 2 0 0 3 1 1 1
  | 5 => tab6N 1 2 1 1 2 0 0 3 1 1 1
  | 6 => tab6N 1 2 2 2 2 0 0 3 1 1 1
  | 7 => tab6N 1 2 2 3 0 0 1 0 0 1 2
  | 8 => tab6N 1 2 2 3 1 0 1 1 0 1 2
  | 9 => tab6N 1 2 2 3 2 0 1 2 0 1 2
  | 10 => tab6N 2 0 1 1 2 0 0 3 1 1 1
  | 11 => tab6N 2 0 2 2 2 0 0 3 1 1 1
  | 12 => tab6N 2 0 2 3 0 0 1 0 0 1 2
  | 13 => tab6N 2 0 2 3 1 0 1 1 0 1 2
  | 14 => tab6N 2 0 2 3 2 0 1 2 0 1 2
  | 15 => tab6N 2 1 0 0 2 0 0 3 1 1 1
  | 16 => tab6N 2 1 1 1 2 0 0 3 1 1 1
  | 17 => tab6N 2 1 2 2 2 0 0 3 1 1 1
  | 18 => tab6N 2 1 2 3 1 0 1 1 0 1 2
  | 19 => tab6N 2 1 2 3 2 0 1 2 0 1 2
  | 20 => tab6N 2 2 1 1 2 0 0 3 1 1 1
  | _ => tab6N 2 2 2 3 1 0 1 1 0 1 2

/-- The arguments as one mixed-radix index, which is how `rankIdx6N` is addressed. -/
def encT6N (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
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

/-- Which of the `22` members a given invariant tuple is, so that `mem_of_isExact6N` can name one
rather than search the list for it. The `41450` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6N` excludes them. Read only by `native_decide`. -/
def rankIdx6N : Nat → Nat
  | 17981 => 0
  | 18406 => 1
  | 22589 => 2
  | 23014 => 3
  | 23357 => 4
  | 25277 => 5
  | 27197 => 6
  | 27334 => 7
  | 27478 => 8
  | 27622 => 9
  | 29885 => 10
  | 31805 => 11
  | 31942 => 12
  | 32086 => 13
  | 32230 => 14
  | 32573 => 15
  | 34493 => 16
  | 36413 => 17
  | 36694 => 18
  | 36838 => 19
  | 39101 => 20
  | 41302 => 21
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6N (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 22 :=
  ⟨min (rankIdx6N (encT6N a b c d e f g h i j k)) 21, by omega⟩


/-- `2` of the `384` demanded maps and `4` of the `46272` forbidden ones, enough to separate the
`22` members from the other `41450` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6N` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6N : Fin 2 → Fin 384
  | 0 => 0
  | 1 => 9
def x0idx6N : Fin 4 → Fin 46272
  | 0 => 0
  | 1 => 18648
  | 2 => 18649
  | 3 => 18666

def endE06N (j : Fin 2) : Fin 6 → Fin 6 := endE6N (e0idx6N j)

def endX06N (j : Fin 4) : Fin 6 → Fin 6 := endX6N (x0idx6N j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6N (i : Fin 22) : Magma (Fin 6) := Magma.mk (mem6N i)

theorem end6N_isEndo (i : Fin 22) (j : Fin 384) : (end6N i).IsEndo (endE6N j) := by
  revert i j; native_decide

theorem end6N_not_isEndo (i : Fin 22) (j : Fin 46272) : ¬ (end6N i).IsEndo (endX6N j) := by
  revert i j; native_decide

/-- `rank6N` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6N` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6N (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6N a b c d e f g h i j k) endE06N endX06N = true) :
    mem6N (rank6N a b c d e f g h i j k) = tab6N a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `22` listed
members. -/
theorem mem_of_isExact6N (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6N a b c d e f g h i j k) endE06N endX06N = true) :
    ∃ idx, mem6N idx = tab6N a b c d e f g h i j k :=
  ⟨_, mem_rank6N a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6N`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6N` turns that into a member index. -/
theorem exists_end6N {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6N j))
    (hX : ∀ j, ¬ M.IsEndo (endX6N j)) : ∃ i, end6N i = M := by
  have hP : ∀ i, M.IsEndo (permE6N i) := by
    intro i; rw [permE6N_eq_endE6N]; exact hE (uidx6N i)
  have hop : M.op = Magma.transport permE6N tr6N (fun i ↦ M.op (rep6N i).1 (rep6N i).2) :=
    Magma.op_eq_transport (rep := rep6N) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N0) (a := (rep6N 0).1) (b := (rep6N 0).2)
    (val := val6N0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N1) (a := (rep6N 1).1) (b := (rep6N 1).2)
    (val := val6N1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N2) (a := (rep6N 2).1) (b := (rep6N 2).2)
    (val := val6N2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N3) (a := (rep6N 3).1) (b := (rep6N 3).2)
    (val := val6N3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N4) (a := (rep6N 4).1) (b := (rep6N 4).2)
    (val := val6N4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N5) (a := (rep6N 5).1) (b := (rep6N 5).2)
    (val := val6N5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N6) (a := (rep6N 6).1) (b := (rep6N 6).2)
    (val := val6N6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N7) (a := (rep6N 7).1) (b := (rep6N 7).2)
    (val := val6N7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N8) (a := (rep6N 8).1) (b := (rep6N 8).2)
    (val := val6N8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N9) (a := (rep6N 9).1) (b := (rep6N 9).2)
    (val := val6N9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6N) (idx := stabIdx6N10) (a := (rep6N 10).1) (b := (rep6N 10).2)
    (val := val6N10) hP (by decide) (by decide)
  have hdec : dec6N a b c d e f g h i j k = fun i ↦ M.op (rep6N i).1 (rep6N i).2 := by
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
  have key : tab6N a b c d e f g h i j k = M.op := by
    rw [tab6N_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6N a b c d e f g h i j k) endE06N endX06N = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6N j), fun j ↦ hX (x0idx6N j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6N a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`384` monoid of `Magma.endE6N`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6N {L L' : Law.NatMagmaLaw} {i : Fin 22}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6N i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6N j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6N i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6N
    (fun k ↦ (Magma.end6N_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6N_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
