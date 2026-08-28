import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `V` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(0 1 2)(3 4 5), (1 2)(4 5)⟩`

`End(M)` is `210` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `8` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(1 2)(4 5)`, `(0 1)(3 4)`, `(0 1 2)(3 4 5)`, `(0 2 1)(3 5
4)`, `(0 2)(3 5)`. -/
def pE6V0 : Fin 6 → Fin 6 := id
def pE6V1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pE6V2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6V3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pE6V4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pE6V5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3

def permE6V : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6V0
  | 1 => pE6V1
  | 2 => pE6V2
  | 3 => pE6V3
  | 4 => pE6V4
  | 5 => pE6V5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `210` self-maps that must be endomorphisms: `000000`, `100000`, `200000`,
`300000`, `010000`, `110000`, `210000`, `020000`, `120000`, `220000`, `030000`, `330000`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6V : Fin 210 → Fin 46656
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 12
  | 8 => 13
  | 9 => 14
  | 10 => 18
  | 11 => 21
  | 12 => 36
  | 13 => 37
  | 14 => 38
  | 15 => 42
  | 16 => 43
  | 17 => 44
  | 18 => 48
  | 19 => 49
  | 20 => 50
  | 21 => 72
  | 22 => 73
  | 23 => 74
  | 24 => 78
  | 25 => 79
  | 26 => 80
  | 27 => 84
  | 28 => 85
  | 29 => 86
  | 30 => 108
  | 31 => 111
  | 32 => 126
  | 33 => 129
  | 34 => 9288
  | 35 => 9289
  | 36 => 9290
  | 37 => 9294
  | 38 => 9295
  | 39 => 9296
  | 40 => 9300
  | 41 => 9301
  | 42 => 9302
  | 43 => 9324
  | 44 => 9325
  | 45 => 9326
  | 46 => 9330
  | 47 => 9331
  | 48 => 9332
  | 49 => 9334
  | 50 => 9336
  | 51 => 9337
  | 52 => 9338
  | 53 => 9349
  | 54 => 9352
  | 55 => 9360
  | 56 => 9361
  | 57 => 9362
  | 58 => 9366
  | 59 => 9367
  | 60 => 9368
  | 61 => 9372
  | 62 => 9373
  | 63 => 9374
  | 64 => 9439
  | 65 => 9442
  | 66 => 9457
  | 67 => 9460
  | 68 => 18576
  | 69 => 18577
  | 70 => 18578
  | 71 => 18582
  | 72 => 18583
  | 73 => 18584
  | 74 => 18588
  | 75 => 18589
  | 76 => 18590
  | 77 => 18612
  | 78 => 18613
  | 79 => 18614
  | 80 => 18618
  | 81 => 18619
  | 82 => 18620
  | 83 => 18624
  | 84 => 18625
  | 85 => 18626
  | 86 => 18648
  | 87 => 18649
  | 88 => 18650
  | 89 => 18654
  | 90 => 18655
  | 91 => 18656
  | 92 => 18660
  | 93 => 18661
  | 94 => 18662
  | 95 => 18665
  | 96 => 18680
  | 97 => 18683
  | 98 => 18770
  | 99 => 18773
  | 100 => 18788
  | 101 => 18791
  | 102 => 27864
  | 103 => 27867
  | 104 => 27882
  | 105 => 27885
  | 106 => 27972
  | 107 => 27975
  | 108 => 27990
  | 109 => 27993
  | 110 => 27994
  | 111 => 27995
  | 112 => 27999
  | 113 => 28000
  | 114 => 28001
  | 115 => 28005
  | 116 => 28006
  | 117 => 28007
  | 118 => 28029
  | 119 => 28030
  | 120 => 28031
  | 121 => 28035
  | 122 => 28036
  | 123 => 28037
  | 124 => 28041
  | 125 => 28042
  | 126 => 28043
  | 127 => 28065
  | 128 => 28066
  | 129 => 28067
  | 130 => 28071
  | 131 => 28072
  | 132 => 28073
  | 133 => 28077
  | 134 => 28078
  | 135 => 28079
  | 136 => 29600
  | 137 => 30685
  | 138 => 36110
  | 139 => 37195
  | 140 => 37198
  | 141 => 37213
  | 142 => 37216
  | 143 => 37281
  | 144 => 37282
  | 145 => 37283
  | 146 => 37287
  | 147 => 37288
  | 148 => 37289
  | 149 => 37293
  | 150 => 37294
  | 151 => 37295
  | 152 => 37303
  | 153 => 37306
  | 154 => 37317
  | 155 => 37318
  | 156 => 37319
  | 157 => 37321
  | 158 => 37323
  | 159 => 37324
  | 160 => 37325
  | 161 => 37329
  | 162 => 37330
  | 163 => 37331
  | 164 => 37353
  | 165 => 37354
  | 166 => 37355
  | 167 => 37359
  | 168 => 37360
  | 169 => 37361
  | 170 => 37365
  | 171 => 37366
  | 172 => 37367
  | 173 => 38280
  | 174 => 43705
  | 175 => 44790
  | 176 => 46526
  | 177 => 46529
  | 178 => 46544
  | 179 => 46547
  | 180 => 46569
  | 181 => 46570
  | 182 => 46571
  | 183 => 46575
  | 184 => 46576
  | 185 => 46577
  | 186 => 46581
  | 187 => 46582
  | 188 => 46583
  | 189 => 46605
  | 190 => 46606
  | 191 => 46607
  | 192 => 46611
  | 193 => 46612
  | 194 => 46613
  | 195 => 46617
  | 196 => 46618
  | 197 => 46619
  | 198 => 46634
  | 199 => 46637
  | 200 => 46641
  | 201 => 46642
  | 202 => 46643
  | 203 => 46647
  | 204 => 46648
  | 205 => 46649
  | 206 => 46652
  | 207 => 46653
  | 208 => 46654
  | _ => 46655

def endE6V (j : Fin 210) : Fin 6 → Fin 6 := allMaps6 (eidx6V j)

/-- Indices of the other `46446`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6V : Array Nat := #[
  0, 1, 2, 3, 6, 7, 8, 12, 13, 14, 18, 21, 36, 37, 38, 42, 43, 44, 48, 49, 50, 72, 73, 74, 78,
  79, 80, 84, 85, 86, 108, 111, 126, 129, 9288, 9289, 9290, 9294, 9295, 9296, 9300, 9301, 9302,
  9324, 9325, 9326, 9330, 9331, 9332, 9334, 9336, 9337, 9338, 9349, 9352, 9360, 9361, 9362, 9366,
  9367, 9368, 9372, 9373, 9374, 9439, 9442, 9457, 9460, 18576, 18577, 18578, 18582, 18583, 18584,
  18588, 18589, 18590, 18612, 18613, 18614, 18618, 18619, 18620, 18624, 18625, 18626, 18648,
  18649, 18650, 18654, 18655, 18656, 18660, 18661, 18662, 18665, 18680, 18683, 18770, 18773,
  18788, 18791, 27864, 27867, 27882, 27885, 27972, 27975, 27990, 27993, 27994, 27995, 27999,
  28000, 28001, 28005, 28006, 28007, 28029, 28030, 28031, 28035, 28036, 28037, 28041, 28042,
  28043, 28065, 28066, 28067, 28071, 28072, 28073, 28077, 28078, 28079, 29600, 30685, 36110,
  37195, 37198, 37213, 37216, 37281, 37282, 37283, 37287, 37288, 37289, 37293, 37294, 37295,
  37303, 37306, 37317, 37318, 37319, 37321, 37323, 37324, 37325, 37329, 37330, 37331, 37353,
  37354, 37355, 37359, 37360, 37361, 37365, 37366, 37367, 38280, 43705, 44790, 46526, 46529,
  46544, 46547, 46569, 46570, 46571, 46575, 46576, 46577, 46581, 46582, 46583, 46605, 46606,
  46607, 46611, 46612, 46613, 46617, 46618, 46619, 46634, 46637, 46641, 46642, 46643, 46647,
  46648, 46649, 46652, 46653, 46654, 46655]

def xarr6V : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6V.contains i)

def xidx6V (j : Fin 46446) : Fin 46656 :=
  ⟨min (xarr6V.getD j.1 0) 46655, by omega⟩

def endX6V (j : Fin 46446) : Fin 6 → Fin 6 := allMaps6 (xidx6V j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6V` is given. -/
def uidx6V : Fin 6 → Fin 210
  | 0 => 175
  | 1 => 173
  | 2 => 174
  | 3 => 137
  | 4 => 138
  | 5 => 136

theorem permE6V_eq_endE6V (i : Fin 6) : permE6V i = endE6V (uidx6V i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `8`, so an invariant
operation is `8` values. -/
def rep6V : Fin 8 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (3, 0)
  | 5 => (3, 1)
  | 6 => (3, 3)
  | 7 => (3, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6V : Fin 6 → Fin 6 → Fin 8 × Fin 6
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 3)
  | 1, 3 => (3, 2)
  | 1, 4 => (2, 2)
  | 1, 5 => (3, 3)
  | 2, 0 => (1, 4)
  | 2, 1 => (1, 5)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 4)
  | 2, 4 => (3, 5)
  | 2, 5 => (2, 4)
  | 3, 0 => (4, 0)
  | 3, 1 => (5, 0)
  | 3, 2 => (5, 1)
  | 3, 3 => (6, 0)
  | 3, 4 => (7, 0)
  | 3, 5 => (7, 1)
  | 4, 0 => (5, 2)
  | 4, 1 => (4, 2)
  | 4, 2 => (5, 3)
  | 4, 3 => (7, 2)
  | 4, 4 => (6, 2)
  | 4, 5 => (7, 3)
  | 5, 0 => (5, 4)
  | 5, 1 => (5, 5)
  | 5, 2 => (4, 4)
  | 5, 3 => (7, 4)
  | 5, 4 => (7, 5)
  | 5, 5 => (6, 4)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6V0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6V0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6V1 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6V2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6V2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6V3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6V4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6V4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6V5 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6V6 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6V6 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6V7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `8` orbit values named by the family's arguments. -/
def dec6V (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 8 → Fin 6
  | 0 => val6V0 a
  | 1 => b
  | 2 => val6V2 c
  | 3 => d
  | 4 => val6V4 e
  | 5 => f
  | 6 => val6V6 g
  | 7 => h

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6V_eq_transport`). -/
def tab6V (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6V0 a
  | 0, 1 => b
  | 0, 2 => pE6V1 b
  | 0, 3 => val6V2 c
  | 0, 4 => d
  | 0, 5 => pE6V1 d
  | 1, 0 => pE6V2 b
  | 1, 1 => pE6V2 (val6V0 a)
  | 1, 2 => pE6V3 b
  | 1, 3 => pE6V2 d
  | 1, 4 => pE6V2 (val6V2 c)
  | 1, 5 => pE6V3 d
  | 2, 0 => pE6V4 b
  | 2, 1 => pE6V5 b
  | 2, 2 => pE6V4 (val6V0 a)
  | 2, 3 => pE6V4 d
  | 2, 4 => pE6V5 d
  | 2, 5 => pE6V4 (val6V2 c)
  | 3, 0 => val6V4 e
  | 3, 1 => f
  | 3, 2 => pE6V1 f
  | 3, 3 => val6V6 g
  | 3, 4 => h
  | 3, 5 => pE6V1 h
  | 4, 0 => pE6V2 f
  | 4, 1 => pE6V2 (val6V4 e)
  | 4, 2 => pE6V3 f
  | 4, 3 => pE6V2 h
  | 4, 4 => pE6V2 (val6V6 g)
  | 4, 5 => pE6V3 h
  | 5, 0 => pE6V4 f
  | 5, 1 => pE6V5 f
  | 5, 2 => pE6V4 (val6V4 e)
  | 5, 3 => pE6V4 h
  | 5, 4 => pE6V5 h
  | 5, 5 => pE6V4 (val6V6 g)

theorem tab6V_eq_transport (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6) :
    tab6V a b c d e f g h = Magma.transport permE6V tr6V (dec6V a b c d e f g h) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `20736` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6V : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6V 0 0 0 0 1 5 1 3
  | 1 => tab6V 0 1 1 5 0 1 1 4

/-- The arguments as one mixed-radix index, which is how `rankIdx6V` is addressed. -/
def encT6V (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Nat :=
  a.1 * 10368 +
    b.1 * 1728 +
    c.1 * 864 +
    d.1 * 144 +
    e.1 * 72 +
    f.1 * 12 +
    g.1 * 6 +
    h.1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6V` can name one
rather than search the list for it. The `20734` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6V` excludes them. Read only by `native_decide`. -/
def rankIdx6V : Nat → Nat
  | 141 => 0
  | 3334 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6V (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 2 :=
  ⟨min (rankIdx6V (encT6V a b c d e f g h)) 1, by omega⟩


/-- `1` of the `210` demanded maps and `1` of the `46446` forbidden ones, enough to separate the `2`
members from the other `20734` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6V` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6V : Fin 1 → Fin 210
  | 0 => 110
def x0idx6V : Fin 1 → Fin 46446
  | 0 => 27945

def endE06V (j : Fin 1) : Fin 6 → Fin 6 := endE6V (e0idx6V j)

def endX06V (j : Fin 1) : Fin 6 → Fin 6 := endX6V (x0idx6V j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6V (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6V i)

theorem end6V_isEndo (i : Fin 2) (j : Fin 210) : (end6V i).IsEndo (endE6V j) := by
  revert i j; native_decide

theorem end6V_not_isEndo (i : Fin 2) (j : Fin 46446) : ¬ (end6V i).IsEndo (endX6V j) := by
  revert i j; native_decide

/-- `rank6V` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6V` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6V (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6)
    (hx : Magma.isExact (tab6V a b c d e f g h) endE06V endX06V = true) :
    mem6V (rank6V a b c d e f g h) = tab6V a b c d e f g h := by
  revert hx; revert a b c d e f g h; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6V (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6)
    (hx : Magma.isExact (tab6V a b c d e f g h) endE06V endX06V = true) :
    ∃ idx, mem6V idx = tab6V a b c d e f g h :=
  ⟨_, mem_rank6V a b c d e f g h hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6V`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6V` turns that into a member index. -/
theorem exists_end6V {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6V j))
    (hX : ∀ j, ¬ M.IsEndo (endX6V j)) : ∃ i, end6V i = M := by
  have hP : ∀ i, M.IsEndo (permE6V i) := by
    intro i; rw [permE6V_eq_endE6V]; exact hE (uidx6V i)
  have hop : M.op = Magma.transport permE6V tr6V (fun i ↦ M.op (rep6V i).1 (rep6V i).2) :=
    Magma.op_eq_transport (rep := rep6V) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V0) (a := (rep6V 0).1) (b := (rep6V 0).2)
    (val := val6V0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V1) (a := (rep6V 1).1) (b := (rep6V 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V2) (a := (rep6V 2).1) (b := (rep6V 2).2)
    (val := val6V2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V3) (a := (rep6V 3).1) (b := (rep6V 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V4) (a := (rep6V 4).1) (b := (rep6V 4).2)
    (val := val6V4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V5) (a := (rep6V 5).1) (b := (rep6V 5).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V6) (a := (rep6V 6).1) (b := (rep6V 6).2)
    (val := val6V6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6V) (idx := stabIdx6V7) (a := (rep6V 7).1) (b := (rep6V 7).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6V a b c d e f g h = fun i ↦ M.op (rep6V i).1 (rep6V i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
  have key : tab6V a b c d e f g h = M.op := by
    rw [tab6V_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6V a b c d e f g h) endE06V endX06V = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6V j), fun j ↦ hX (x0idx6V j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6V a b c d e f g h hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`210` monoid of `Magma.endE6V`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6V {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6V i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6V j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6V i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6V
    (fun k ↦ (Magma.end6V_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6V_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
