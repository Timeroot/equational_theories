import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `P` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(2 3)(4 5), (0 2)(4 5)⟩`

`End(M)` is `114` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(2 3)(4 5)`, `(0 2)(4 5)`, `(0 2 3)`, `(0 3 2)`, `(0 3)(4
5)`. -/
def pE6P0 : Fin 6 → Fin 6 := id
def pE6P1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6P2 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pE6P3 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5
def pE6P4 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5
def pE6P5 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4

def permE6P : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6P0
  | 1 => pE6P1
  | 2 => pE6P2
  | 3 => pE6P3
  | 4 => pE6P4
  | 5 => pE6P5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `114` self-maps that must be endomorphisms: `010011`, `110011`, `410011`,
`510011`, `011011`, `111011`, `411011`, `511011`, `014011`, `114011`, `414011`, `015011`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6P : Fin 114 → Fin 46656
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
  | 11 => 9258
  | 12 => 9259
  | 13 => 9263
  | 14 => 9294
  | 15 => 9295
  | 16 => 9298
  | 17 => 9299
  | 18 => 9330
  | 19 => 9331
  | 20 => 9332
  | 21 => 9333
  | 22 => 9334
  | 23 => 9335
  | 24 => 9367
  | 25 => 9368
  | 26 => 9370
  | 27 => 9371
  | 28 => 9403
  | 29 => 9405
  | 30 => 9406
  | 31 => 9407
  | 32 => 9438
  | 33 => 9439
  | 34 => 9440
  | 35 => 9441
  | 36 => 9442
  | 37 => 9474
  | 38 => 9475
  | 39 => 9476
  | 40 => 9477
  | 41 => 9479
  | 42 => 9547
  | 43 => 9548
  | 44 => 9550
  | 45 => 9551
  | 46 => 9583
  | 47 => 9584
  | 48 => 9586
  | 49 => 9587
  | 50 => 9655
  | 51 => 9656
  | 52 => 9658
  | 53 => 9691
  | 54 => 9692
  | 55 => 9695
  | 56 => 9763
  | 57 => 9765
  | 58 => 9766
  | 59 => 9767
  | 60 => 9835
  | 61 => 9837
  | 62 => 9838
  | 63 => 9839
  | 64 => 9871
  | 65 => 9873
  | 66 => 9874
  | 67 => 9907
  | 68 => 9909
  | 69 => 9911
  | 70 => 9942
  | 71 => 9943
  | 72 => 9946
  | 73 => 9978
  | 74 => 9979
  | 75 => 9980
  | 76 => 9981
  | 77 => 9982
  | 78 => 10015
  | 79 => 10016
  | 80 => 10018
  | 81 => 10051
  | 82 => 10053
  | 83 => 10054
  | 84 => 10086
  | 85 => 10087
  | 86 => 10088
  | 87 => 10089
  | 88 => 10090
  | 89 => 10158
  | 90 => 10159
  | 91 => 10163
  | 92 => 10194
  | 93 => 10195
  | 94 => 10196
  | 95 => 10197
  | 96 => 10199
  | 97 => 10231
  | 98 => 10232
  | 99 => 10235
  | 100 => 10267
  | 101 => 10269
  | 102 => 10271
  | 103 => 10338
  | 104 => 10339
  | 105 => 10340
  | 106 => 10341
  | 107 => 10343
  | 108 => 37665
  | 109 => 38130
  | 110 => 38240
  | 111 => 44180
  | 112 => 44505
  | _ => 44790

def endE6P (j : Fin 114) : Fin 6 → Fin 6 := allMaps6 (eidx6P j)

/-- Indices of the other `46542`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6P : Array Nat := #[
  9078, 9079, 9082, 9083, 9114, 9115, 9118, 9119, 9222, 9223, 9226, 9258, 9259, 9263, 9294, 9295,
  9298, 9299, 9330, 9331, 9332, 9333, 9334, 9335, 9367, 9368, 9370, 9371, 9403, 9405, 9406, 9407,
  9438, 9439, 9440, 9441, 9442, 9474, 9475, 9476, 9477, 9479, 9547, 9548, 9550, 9551, 9583, 9584,
  9586, 9587, 9655, 9656, 9658, 9691, 9692, 9695, 9763, 9765, 9766, 9767, 9835, 9837, 9838, 9839,
  9871, 9873, 9874, 9907, 9909, 9911, 9942, 9943, 9946, 9978, 9979, 9980, 9981, 9982, 10015,
  10016, 10018, 10051, 10053, 10054, 10086, 10087, 10088, 10089, 10090, 10158, 10159, 10163,
  10194, 10195, 10196, 10197, 10199, 10231, 10232, 10235, 10267, 10269, 10271, 10338, 10339,
  10340, 10341, 10343, 37665, 38130, 38240, 44180, 44505, 44790]

def xarr6P : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6P.contains i)

def xidx6P (j : Fin 46542) : Fin 46656 :=
  ⟨min (xarr6P.getD j.1 0) 46655, by omega⟩

def endX6P (j : Fin 46542) : Fin 6 → Fin 6 := allMaps6 (xidx6P j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6P` is given. -/
def uidx6P : Fin 6 → Fin 114
  | 0 => 113
  | 1 => 109
  | 2 => 110
  | 3 => 111
  | 4 => 112
  | 5 => 108

theorem permE6P_eq_endE6P (i : Fin 6) : permE6P i = endE6P (uidx6P i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6P : Fin 11 → Fin 6 × Fin 6
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
def tr6P : Fin 6 → Fin 6 → Fin 11 × Fin 6
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
def stabIdx6P0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6P0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6P1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6P1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6P2 : Fin 1 → Fin 6
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6P3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6P4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6P4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `1`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6P5 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6P5 : Fin 1 → Fin 6
  | 0 => 1

/-- The `3` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6P6 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6P6 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6P7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6P8 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6P8 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6P9 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6P9 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6P10 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6P10 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6P (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 11 → Fin 6
  | 0 => val6P0 a
  | 1 => val6P1 b
  | 2 => c
  | 3 => d
  | 4 => val6P4 e
  | 5 => val6P5 f
  | 6 => val6P6 g
  | 7 => h
  | 8 => val6P8 i
  | 9 => val6P9 j
  | 10 => val6P10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6P_eq_transport`). -/
def tab6P (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6P0 a
  | 0, 1 => val6P1 b
  | 0, 2 => c
  | 0, 3 => pE6P1 c
  | 0, 4 => d
  | 0, 5 => pE6P1 d
  | 1, 0 => val6P4 e
  | 1, 1 => val6P5 f
  | 1, 2 => pE6P2 (val6P4 e)
  | 1, 3 => pE6P4 (val6P4 e)
  | 1, 4 => val6P6 g
  | 1, 5 => pE6P1 (val6P6 g)
  | 2, 0 => pE6P2 c
  | 2, 1 => pE6P2 (val6P1 b)
  | 2, 2 => pE6P2 (val6P0 a)
  | 2, 3 => pE6P3 c
  | 2, 4 => pE6P3 d
  | 2, 5 => pE6P2 d
  | 3, 0 => pE6P4 c
  | 3, 1 => pE6P4 (val6P1 b)
  | 3, 2 => pE6P5 c
  | 3, 3 => pE6P4 (val6P0 a)
  | 3, 4 => pE6P4 d
  | 3, 5 => pE6P5 d
  | 4, 0 => h
  | 4, 1 => val6P8 i
  | 4, 2 => pE6P3 h
  | 4, 3 => pE6P4 h
  | 4, 4 => val6P9 j
  | 4, 5 => val6P10 k
  | 5, 0 => pE6P1 h
  | 5, 1 => pE6P1 (val6P8 i)
  | 5, 2 => pE6P2 h
  | 5, 3 => pE6P5 h
  | 5, 4 => pE6P1 (val6P10 k)
  | 5, 5 => pE6P1 (val6P9 j)

theorem tab6P_eq_transport (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3)
    (h : Fin 6) (i j k : Fin 3) :
    tab6P a b c d e f g h i j k = Magma.transport permE6P tr6P (dec6P a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `139968` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6P : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6P 1 1 4 1 1 0 0 1 0 0 1
  | 1 => tab6P 1 1 4 1 1 0 0 1 0 0 2
  | 2 => tab6P 1 1 5 1 1 0 0 1 0 0 1
  | 3 => tab6P 1 1 5 1 1 0 0 1 0 0 2

/-- The arguments as one mixed-radix index, which is how `rankIdx6P` is addressed. -/
def encT6P (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
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

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6P` can name one
rather than search the list for it. The `139964` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6P` excludes them. Read only by `native_decide`. -/
def rankIdx6P : Nat → Nat
  | 129790 => 0
  | 129791 => 1
  | 135622 => 2
  | 135623 => 3
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6P (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 4 :=
  ⟨min (rankIdx6P (encT6P a b c d e f g h i j k)) 3, by omega⟩


/-- `1` of the `114` demanded maps and `2` of the `46542` forbidden ones, enough to separate the `4`
members from the other `139964` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6P` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6P : Fin 1 → Fin 114
  | 0 => 2
def x0idx6P : Fin 2 → Fin 46542
  | 0 => 9078
  | 1 => 9216

def endE06P (j : Fin 1) : Fin 6 → Fin 6 := endE6P (e0idx6P j)

def endX06P (j : Fin 2) : Fin 6 → Fin 6 := endX6P (x0idx6P j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6P (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6P i)

theorem end6P_isEndo (i : Fin 4) (j : Fin 114) : (end6P i).IsEndo (endE6P j) := by
  revert i j; native_decide

theorem end6P_not_isEndo (i : Fin 4) (j : Fin 46542) : ¬ (end6P i).IsEndo (endX6P j) := by
  revert i j; native_decide

/-- `rank6P` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6P` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6P (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6P a b c d e f g h i j k) endE06P endX06P = true) :
    mem6P (rank6P a b c d e f g h i j k) = tab6P a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6P (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6P a b c d e f g h i j k) endE06P endX06P = true) :
    ∃ idx, mem6P idx = tab6P a b c d e f g h i j k :=
  ⟨_, mem_rank6P a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6P`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6P` turns that into a member index. -/
theorem exists_end6P {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6P j))
    (hX : ∀ j, ¬ M.IsEndo (endX6P j)) : ∃ i, end6P i = M := by
  have hP : ∀ i, M.IsEndo (permE6P i) := by
    intro i; rw [permE6P_eq_endE6P]; exact hE (uidx6P i)
  have hop : M.op = Magma.transport permE6P tr6P (fun i ↦ M.op (rep6P i).1 (rep6P i).2) :=
    Magma.op_eq_transport (rep := rep6P) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P0) (a := (rep6P 0).1) (b := (rep6P 0).2)
    (val := val6P0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P1) (a := (rep6P 1).1) (b := (rep6P 1).2)
    (val := val6P1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P2) (a := (rep6P 2).1) (b := (rep6P 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P3) (a := (rep6P 3).1) (b := (rep6P 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P4) (a := (rep6P 4).1) (b := (rep6P 4).2)
    (val := val6P4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P5) (a := (rep6P 5).1) (b := (rep6P 5).2)
    (val := val6P5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P6) (a := (rep6P 6).1) (b := (rep6P 6).2)
    (val := val6P6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P7) (a := (rep6P 7).1) (b := (rep6P 7).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P8) (a := (rep6P 8).1) (b := (rep6P 8).2)
    (val := val6P8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P9) (a := (rep6P 9).1) (b := (rep6P 9).2)
    (val := val6P9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6P) (idx := stabIdx6P10) (a := (rep6P 10).1) (b := (rep6P 10).2)
    (val := val6P10) hP (by decide) (by decide)
  have hdec : dec6P a b c d e f g h i j k = fun i ↦ M.op (rep6P i).1 (rep6P i).2 := by
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
  have key : tab6P a b c d e f g h i j k = M.op := by
    rw [tab6P_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6P a b c d e f g h i j k) endE06P endX06P = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6P j), fun j ↦ hX (x0idx6P j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6P a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`114` monoid of `Magma.endE6P`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6P {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6P i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6P j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6P i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6P
    (fun k ↦ (Magma.end6P_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6P_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
