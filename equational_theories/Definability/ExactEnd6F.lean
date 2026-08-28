import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `F` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(2 3)(4 5), (0 2)(4 5)⟩`

`End(M)` is `144` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(2 3)(4 5)`, `(0 2)(4 5)`, `(0 2 3)`, `(0 3 2)`, `(0 3)(4
5)`. -/
def pE6F0 : Fin 6 → Fin 6 := id
def pE6F1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6F2 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pE6F3 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5
def pE6F4 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5
def pE6F5 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4

def permE6F : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6F0
  | 1 => pE6F1
  | 2 => pE6F2
  | 3 => pE6F3
  | 4 => pE6F4
  | 5 => pE6F5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `144` self-maps that must be endomorphisms: `010011`, `110011`, `410011`,
`510011`, `011011`, `111011`, `411011`, `511011`, `014011`, `114011`, `414011`, `514011`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6F : Fin 144 → Fin 46656
  | 0 => 9078
  | 1 => 9079
  | 2 => 9082
  | 3 => 9083
  | 4 => 9114
  | 5 => 9115
  | 6 => 9118
  | 7 => 9119
  | 8 => 9222
  | 9 => 9223
  | 10 => 9226
  | 11 => 9227
  | 12 => 9258
  | 13 => 9259
  | 14 => 9262
  | 15 => 9263
  | 16 => 9294
  | 17 => 9295
  | 18 => 9298
  | 19 => 9299
  | 20 => 9330
  | 21 => 9331
  | 22 => 9332
  | 23 => 9333
  | 24 => 9334
  | 25 => 9335
  | 26 => 9367
  | 27 => 9368
  | 28 => 9370
  | 29 => 9371
  | 30 => 9403
  | 31 => 9405
  | 32 => 9406
  | 33 => 9407
  | 34 => 9438
  | 35 => 9439
  | 36 => 9440
  | 37 => 9441
  | 38 => 9442
  | 39 => 9443
  | 40 => 9474
  | 41 => 9475
  | 42 => 9476
  | 43 => 9477
  | 44 => 9478
  | 45 => 9479
  | 46 => 9547
  | 47 => 9548
  | 48 => 9550
  | 49 => 9551
  | 50 => 9583
  | 51 => 9584
  | 52 => 9586
  | 53 => 9587
  | 54 => 9655
  | 55 => 9656
  | 56 => 9658
  | 57 => 9659
  | 58 => 9691
  | 59 => 9692
  | 60 => 9694
  | 61 => 9695
  | 62 => 9763
  | 63 => 9765
  | 64 => 9766
  | 65 => 9767
  | 66 => 9835
  | 67 => 9837
  | 68 => 9838
  | 69 => 9839
  | 70 => 9871
  | 71 => 9873
  | 72 => 9874
  | 73 => 9875
  | 74 => 9907
  | 75 => 9909
  | 76 => 9910
  | 77 => 9911
  | 78 => 9942
  | 79 => 9943
  | 80 => 9946
  | 81 => 9947
  | 82 => 9978
  | 83 => 9979
  | 84 => 9980
  | 85 => 9981
  | 86 => 9982
  | 87 => 9983
  | 88 => 10015
  | 89 => 10016
  | 90 => 10018
  | 91 => 10019
  | 92 => 10051
  | 93 => 10053
  | 94 => 10054
  | 95 => 10055
  | 96 => 10086
  | 97 => 10087
  | 98 => 10088
  | 99 => 10089
  | 100 => 10090
  | 101 => 10091
  | 102 => 10122
  | 103 => 10123
  | 104 => 10124
  | 105 => 10125
  | 106 => 10126
  | 107 => 10127
  | 108 => 10158
  | 109 => 10159
  | 110 => 10162
  | 111 => 10163
  | 112 => 10194
  | 113 => 10195
  | 114 => 10196
  | 115 => 10197
  | 116 => 10198
  | 117 => 10199
  | 118 => 10231
  | 119 => 10232
  | 120 => 10234
  | 121 => 10235
  | 122 => 10267
  | 123 => 10269
  | 124 => 10270
  | 125 => 10271
  | 126 => 10302
  | 127 => 10303
  | 128 => 10304
  | 129 => 10305
  | 130 => 10306
  | 131 => 10307
  | 132 => 10338
  | 133 => 10339
  | 134 => 10340
  | 135 => 10341
  | 136 => 10342
  | 137 => 10343
  | 138 => 37665
  | 139 => 38130
  | 140 => 38240
  | 141 => 44180
  | 142 => 44505
  | _ => 44790

def endE6F (j : Fin 144) : Fin 6 → Fin 6 := allMaps6 (eidx6F j)

/-- Indices of the other `46512`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6F : Array Nat := #[
  9078, 9079, 9082, 9083, 9114, 9115, 9118, 9119, 9222, 9223, 9226, 9227, 9258, 9259, 9262, 9263,
  9294, 9295, 9298, 9299, 9330, 9331, 9332, 9333, 9334, 9335, 9367, 9368, 9370, 9371, 9403, 9405,
  9406, 9407, 9438, 9439, 9440, 9441, 9442, 9443, 9474, 9475, 9476, 9477, 9478, 9479, 9547, 9548,
  9550, 9551, 9583, 9584, 9586, 9587, 9655, 9656, 9658, 9659, 9691, 9692, 9694, 9695, 9763, 9765,
  9766, 9767, 9835, 9837, 9838, 9839, 9871, 9873, 9874, 9875, 9907, 9909, 9910, 9911, 9942, 9943,
  9946, 9947, 9978, 9979, 9980, 9981, 9982, 9983, 10015, 10016, 10018, 10019, 10051, 10053,
  10054, 10055, 10086, 10087, 10088, 10089, 10090, 10091, 10122, 10123, 10124, 10125, 10126,
  10127, 10158, 10159, 10162, 10163, 10194, 10195, 10196, 10197, 10198, 10199, 10231, 10232,
  10234, 10235, 10267, 10269, 10270, 10271, 10302, 10303, 10304, 10305, 10306, 10307, 10338,
  10339, 10340, 10341, 10342, 10343, 37665, 38130, 38240, 44180, 44505, 44790]

def xarr6F : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6F.contains i)

def xidx6F (j : Fin 46512) : Fin 46656 :=
  ⟨min (xarr6F.getD j.1 0) 46655, by omega⟩

def endX6F (j : Fin 46512) : Fin 6 → Fin 6 := allMaps6 (xidx6F j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6F` is given. -/
def uidx6F : Fin 6 → Fin 144
  | 0 => 143
  | 1 => 139
  | 2 => 140
  | 3 => 141
  | 4 => 142
  | 5 => 138

theorem permE6F_eq_endE6F (i : Fin 6) : permE6F i = endE6F (uidx6F i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6F : Fin 11 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (1, 0)
  | 5 => (1, 1)
  | 6 => (1, 4)
  | 7 => (4, 0)
  | 8 => (4, 1)
  | 9 => (4, 4)
  | 10 => (4, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6F : Fin 6 → Fin 6 → Fin 11 × Fin 6
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (4, 0)
  | 1, 1 => (5, 0)
  | 1, 2 => (4, 2)
  | 1, 3 => (4, 4)
  | 1, 4 => (6, 0)
  | 1, 5 => (6, 1)
  | 2, 0 => (2, 2)
  | 2, 1 => (1, 2)
  | 2, 2 => (0, 2)
  | 2, 3 => (2, 3)
  | 2, 4 => (3, 3)
  | 2, 5 => (3, 2)
  | 3, 0 => (2, 4)
  | 3, 1 => (1, 4)
  | 3, 2 => (2, 5)
  | 3, 3 => (0, 4)
  | 3, 4 => (3, 4)
  | 3, 5 => (3, 5)
  | 4, 0 => (7, 0)
  | 4, 1 => (8, 0)
  | 4, 2 => (7, 3)
  | 4, 3 => (7, 4)
  | 4, 4 => (9, 0)
  | 4, 5 => (10, 0)
  | 5, 0 => (7, 1)
  | 5, 1 => (8, 1)
  | 5, 2 => (7, 2)
  | 5, 3 => (7, 5)
  | 5, 4 => (10, 1)
  | 5, 5 => (9, 1)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6F0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6F0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6F1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6F1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6F2 : Fin 1 → Fin 6
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6F3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6F4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6F4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `1`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6F5 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6F5 : Fin 1 → Fin 6
  | 0 => 1

/-- The `3` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6F6 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6F6 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6F7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6F8 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6F8 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6F9 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6F9 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6F10 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6F10 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6F (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 11 → Fin 6
  | 0 => val6F0 a
  | 1 => val6F1 b
  | 2 => c
  | 3 => d
  | 4 => val6F4 e
  | 5 => val6F5 f
  | 6 => val6F6 g
  | 7 => h
  | 8 => val6F8 i
  | 9 => val6F9 j
  | 10 => val6F10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6F_eq_transport`). -/
def tab6F (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6F0 a
  | 0, 1 => val6F1 b
  | 0, 2 => c
  | 0, 3 => pE6F1 c
  | 0, 4 => d
  | 0, 5 => pE6F1 d
  | 1, 0 => val6F4 e
  | 1, 1 => val6F5 f
  | 1, 2 => pE6F2 (val6F4 e)
  | 1, 3 => pE6F4 (val6F4 e)
  | 1, 4 => val6F6 g
  | 1, 5 => pE6F1 (val6F6 g)
  | 2, 0 => pE6F2 c
  | 2, 1 => pE6F2 (val6F1 b)
  | 2, 2 => pE6F2 (val6F0 a)
  | 2, 3 => pE6F3 c
  | 2, 4 => pE6F3 d
  | 2, 5 => pE6F2 d
  | 3, 0 => pE6F4 c
  | 3, 1 => pE6F4 (val6F1 b)
  | 3, 2 => pE6F5 c
  | 3, 3 => pE6F4 (val6F0 a)
  | 3, 4 => pE6F4 d
  | 3, 5 => pE6F5 d
  | 4, 0 => h
  | 4, 1 => val6F8 i
  | 4, 2 => pE6F3 h
  | 4, 3 => pE6F4 h
  | 4, 4 => val6F9 j
  | 4, 5 => val6F10 k
  | 5, 0 => pE6F1 h
  | 5, 1 => pE6F1 (val6F8 i)
  | 5, 2 => pE6F2 h
  | 5, 3 => pE6F5 h
  | 5, 4 => pE6F1 (val6F10 k)
  | 5, 5 => pE6F1 (val6F9 j)

theorem tab6F_eq_transport (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3)
    (h : Fin 6) (i j k : Fin 3) :
    tab6F a b c d e f g h i j k = Magma.transport permE6F tr6F (dec6F a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `139968` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6F : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6F 1 1 4 1 1 0 0 1 0 0 0
  | 1 => tab6F 1 1 5 1 1 0 0 1 0 0 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6F` is addressed. -/
def encT6F (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Nat :=
  a.1 * 69984 +
    b.1 * 34992 +
    c.1 * 5832 +
    d.1 * 972 +
    e.1 * 486 +
    f.1 * 486 +
    g.1 * 162 +
    h.1 * 27 +
    i.1 * 9 +
    j.1 * 3 +
    k.1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6F` can name one
rather than search the list for it. The `139966` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6F` excludes them. Read only by `native_decide`. -/
def rankIdx6F : Nat → Nat
  | 129789 => 0
  | 135621 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6F (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 2 :=
  ⟨min (rankIdx6F (encT6F a b c d e f g h i j k)) 1, by omega⟩


/-- `2` of the `144` demanded maps and `1` of the `46512` forbidden ones, enough to separate the `2`
members from the other `139966` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6F` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6F : Fin 2 → Fin 144
  | 0 => 2
  | 1 => 11
def x0idx6F : Fin 1 → Fin 46512
  | 0 => 6

def endE06F (j : Fin 2) : Fin 6 → Fin 6 := endE6F (e0idx6F j)

def endX06F (j : Fin 1) : Fin 6 → Fin 6 := endX6F (x0idx6F j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6F (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6F i)

theorem end6F_isEndo (i : Fin 2) (j : Fin 144) : (end6F i).IsEndo (endE6F j) := by
  revert i j; native_decide

theorem end6F_not_isEndo (i : Fin 2) (j : Fin 46512) : ¬ (end6F i).IsEndo (endX6F j) := by
  revert i j; native_decide

/-- `rank6F` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6F` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6F (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6F a b c d e f g h i j k) endE06F endX06F = true) :
    mem6F (rank6F a b c d e f g h i j k) = tab6F a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6F (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6F a b c d e f g h i j k) endE06F endX06F = true) :
    ∃ idx, mem6F idx = tab6F a b c d e f g h i j k :=
  ⟨_, mem_rank6F a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6F`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6F` turns that into a member index. -/
theorem exists_end6F {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6F j))
    (hX : ∀ j, ¬ M.IsEndo (endX6F j)) : ∃ i, end6F i = M := by
  have hP : ∀ i, M.IsEndo (permE6F i) := by
    intro i; rw [permE6F_eq_endE6F]; exact hE (uidx6F i)
  have hop : M.op = Magma.transport permE6F tr6F (fun i ↦ M.op (rep6F i).1 (rep6F i).2) :=
    Magma.op_eq_transport (rep := rep6F) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F0) (a := (rep6F 0).1) (b := (rep6F 0).2)
    (val := val6F0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F1) (a := (rep6F 1).1) (b := (rep6F 1).2)
    (val := val6F1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F2) (a := (rep6F 2).1) (b := (rep6F 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F3) (a := (rep6F 3).1) (b := (rep6F 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F4) (a := (rep6F 4).1) (b := (rep6F 4).2)
    (val := val6F4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F5) (a := (rep6F 5).1) (b := (rep6F 5).2)
    (val := val6F5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F6) (a := (rep6F 6).1) (b := (rep6F 6).2)
    (val := val6F6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F7) (a := (rep6F 7).1) (b := (rep6F 7).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F8) (a := (rep6F 8).1) (b := (rep6F 8).2)
    (val := val6F8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F9) (a := (rep6F 9).1) (b := (rep6F 9).2)
    (val := val6F9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6F) (idx := stabIdx6F10) (a := (rep6F 10).1) (b := (rep6F 10).2)
    (val := val6F10) hP (by decide) (by decide)
  have hdec : dec6F a b c d e f g h i j k = fun i ↦ M.op (rep6F i).1 (rep6F i).2 := by
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
  have key : tab6F a b c d e f g h i j k = M.op := by
    rw [tab6F_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6F a b c d e f g h i j k) endE06F endX06F = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6F j), fun j ↦ hX (x0idx6F j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6F a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`144` monoid of `Magma.endE6F`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6F {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6F i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6F j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6F i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6F
    (fun k ↦ (Magma.end6F_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6F_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
