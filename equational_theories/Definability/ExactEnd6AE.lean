import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AE` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `58` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6AE0 : Fin 6 → Fin 6 := id
def pE6AE1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AE2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AE3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AE4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AE5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6AE6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6AE7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AE8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AE9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AE10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AE11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6AE : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6AE0
  | 1 => pE6AE1
  | 2 => pE6AE2
  | 3 => pE6AE3
  | 4 => pE6AE4
  | 5 => pE6AE5
  | 6 => pE6AE6
  | 7 => pE6AE7
  | 8 => pE6AE8
  | 9 => pE6AE9
  | 10 => pE6AE10
  | 11 => pE6AE11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `58` self-maps that must be endomorphisms: `222210`, `222120`, `222220`,
`222201`, `222021`, `222221`, `222102`, `222202`, `222012`, `222212`, `222022`, `222122`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AE : Fin 58 → Fin 46656
  | 0 => 1814
  | 1 => 2894
  | 2 => 3110
  | 3 => 8294
  | 4 => 10454
  | 5 => 10886
  | 6 => 15854
  | 7 => 16070
  | 8 => 16934
  | 9 => 17366
  | 10 => 18230
  | 11 => 18446
  | 12 => 18662
  | 13 => 18878
  | 14 => 19094
  | 15 => 19310
  | 16 => 19958
  | 17 => 20390
  | 18 => 20606
  | 19 => 21254
  | 20 => 21470
  | 21 => 21902
  | 22 => 22550
  | 23 => 22766
  | 24 => 22982
  | 25 => 26438
  | 26 => 26870
  | 27 => 27086
  | 28 => 29030
  | 29 => 29665
  | 30 => 29670
  | 31 => 29678
  | 32 => 30326
  | 33 => 30745
  | 34 => 30750
  | 35 => 30758
  | 36 => 34214
  | 37 => 34430
  | 38 => 34862
  | 39 => 35510
  | 40 => 36145
  | 41 => 36150
  | 42 => 36158
  | 43 => 38102
  | 44 => 38305
  | 45 => 38310
  | 46 => 38318
  | 47 => 41990
  | 48 => 42206
  | 49 => 42422
  | 50 => 43286
  | 51 => 43705
  | 52 => 43710
  | 53 => 43718
  | 54 => 44582
  | 55 => 44785
  | 56 => 44790
  | _ => 44798

def endE6AE (j : Fin 58) : Fin 6 → Fin 6 := allMaps6 (eidx6AE j)

/-- Indices of the other `46598`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AE : Array Nat := #[
  1814, 2894, 3110, 8294, 10454, 10886, 15854, 16070, 16934, 17366, 18230, 18446, 18662, 18878,
  19094, 19310, 19958, 20390, 20606, 21254, 21470, 21902, 22550, 22766, 22982, 26438, 26870,
  27086, 29030, 29665, 29670, 29678, 30326, 30745, 30750, 30758, 34214, 34430, 34862, 35510,
  36145, 36150, 36158, 38102, 38305, 38310, 38318, 41990, 42206, 42422, 43286, 43705, 43710,
  43718, 44582, 44785, 44790, 44798]

def xarr6AE : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AE.contains i)

def xidx6AE (j : Fin 46598) : Fin 46656 :=
  ⟨min (xarr6AE.getD j.1 0) 46655, by omega⟩

def endX6AE (j : Fin 46598) : Fin 6 → Fin 6 := allMaps6 (xidx6AE j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AE` is given. -/
def uidx6AE : Fin 12 → Fin 58
  | 0 => 56
  | 1 => 45
  | 2 => 52
  | 3 => 34
  | 4 => 41
  | 5 => 30
  | 6 => 55
  | 7 => 44
  | 8 => 51
  | 9 => 33
  | 10 => 40
  | 11 => 29

theorem permE6AE_eq_endE6AE (i : Fin 12) : permE6AE i = endE6AE (uidx6AE i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6AE : Fin 11 → Fin 6 × Fin 6
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
def tr6AE : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6AE0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AE0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AE1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AE1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AE2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AE2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AE3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AE3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AE4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AE4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6AE5 : Fin 12 → Fin 12
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
def val6AE5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AE6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AE6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AE7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AE7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AE8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AE8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AE9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AE9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AE10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6AE10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6AE (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6AE0 a
  | 1 => val6AE1 b
  | 2 => val6AE2 c
  | 3 => val6AE3 d
  | 4 => val6AE4 e
  | 5 => val6AE5 f
  | 6 => val6AE6 g
  | 7 => val6AE7 h
  | 8 => val6AE8 i
  | 9 => val6AE9 j
  | 10 => val6AE10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AE_eq_transport`). -/
def tab6AE (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AE0 a
  | 0, 1 => val6AE1 b
  | 0, 2 => val6AE2 c
  | 0, 3 => val6AE3 d
  | 0, 4 => pE6AE2 (val6AE3 d)
  | 0, 5 => pE6AE4 (val6AE3 d)
  | 1, 0 => pE6AE6 (val6AE1 b)
  | 1, 1 => pE6AE6 (val6AE0 a)
  | 1, 2 => pE6AE6 (val6AE2 c)
  | 1, 3 => pE6AE6 (val6AE3 d)
  | 1, 4 => pE6AE8 (val6AE3 d)
  | 1, 5 => pE6AE10 (val6AE3 d)
  | 2, 0 => val6AE4 e
  | 2, 1 => pE6AE6 (val6AE4 e)
  | 2, 2 => val6AE5 f
  | 2, 3 => val6AE6 g
  | 2, 4 => pE6AE2 (val6AE6 g)
  | 2, 5 => pE6AE4 (val6AE6 g)
  | 3, 0 => val6AE7 h
  | 3, 1 => pE6AE6 (val6AE7 h)
  | 3, 2 => val6AE8 i
  | 3, 3 => val6AE9 j
  | 3, 4 => val6AE10 k
  | 3, 5 => pE6AE1 (val6AE10 k)
  | 4, 0 => pE6AE2 (val6AE7 h)
  | 4, 1 => pE6AE8 (val6AE7 h)
  | 4, 2 => pE6AE2 (val6AE8 i)
  | 4, 3 => pE6AE2 (val6AE10 k)
  | 4, 4 => pE6AE2 (val6AE9 j)
  | 4, 5 => pE6AE3 (val6AE10 k)
  | 5, 0 => pE6AE4 (val6AE7 h)
  | 5, 1 => pE6AE10 (val6AE7 h)
  | 5, 2 => pE6AE4 (val6AE8 i)
  | 5, 3 => pE6AE4 (val6AE10 k)
  | 5, 4 => pE6AE5 (val6AE10 k)
  | 5, 5 => pE6AE4 (val6AE9 j)

theorem tab6AE_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6AE a b c d e f g h i j k = Magma.transport permE6AE tr6AE (dec6AE a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AE : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AE 2 0 0 1 2 0 0 3 1 0 1
  | 1 => tab6AE 2 1 2 3 0 0 1 1 0 0 2

/-- The arguments as one mixed-radix index, which is how `rankIdx6AE` is addressed. -/
def encT6AE (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
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

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6AE` can name one
rather than search the list for it. The `41470` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6AE` excludes them. Read only by `native_decide`. -/
def rankIdx6AE : Nat → Nat
  | 28345 => 0
  | 36562 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AE (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4) : Fin 2 :=
  ⟨min (rankIdx6AE (encT6AE a b c d e f g h i j k)) 1, by omega⟩


/-- `1` of the `58` demanded maps and `3` of the `46598` forbidden ones, enough to separate the `2`
members from the other `41470` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AE` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AE : Fin 1 → Fin 58
  | 0 => 0
def x0idx6AE : Fin 3 → Fin 46598
  | 0 => 0
  | 1 => 86
  | 2 => 29636

def endE06AE (j : Fin 1) : Fin 6 → Fin 6 := endE6AE (e0idx6AE j)

def endX06AE (j : Fin 3) : Fin 6 → Fin 6 := endX6AE (x0idx6AE j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AE (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6AE i)

theorem end6AE_isEndo (i : Fin 2) (j : Fin 58) : (end6AE i).IsEndo (endE6AE j) := by
  revert i j; native_decide

theorem end6AE_not_isEndo (i : Fin 2) (j : Fin 46598) : ¬ (end6AE i).IsEndo (endX6AE j) := by
  revert i j; native_decide

/-- `rank6AE` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AE` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AE (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AE a b c d e f g h i j k) endE06AE endX06AE = true) :
    mem6AE (rank6AE a b c d e f g h i j k) = tab6AE a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6AE (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AE a b c d e f g h i j k) endE06AE endX06AE = true) :
    ∃ idx, mem6AE idx = tab6AE a b c d e f g h i j k :=
  ⟨_, mem_rank6AE a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AE`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AE` turns that into a member index. -/
theorem exists_end6AE {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AE j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AE j)) : ∃ i, end6AE i = M := by
  have hP : ∀ i, M.IsEndo (permE6AE i) := by
    intro i; rw [permE6AE_eq_endE6AE]; exact hE (uidx6AE i)
  have hop : M.op = Magma.transport permE6AE tr6AE (fun i ↦ M.op (rep6AE i).1 (rep6AE i).2) :=
    Magma.op_eq_transport (rep := rep6AE) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE0) (a := (rep6AE 0).1) (b := (rep6AE 0).2)
    (val := val6AE0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE1) (a := (rep6AE 1).1) (b := (rep6AE 1).2)
    (val := val6AE1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE2) (a := (rep6AE 2).1) (b := (rep6AE 2).2)
    (val := val6AE2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE3) (a := (rep6AE 3).1) (b := (rep6AE 3).2)
    (val := val6AE3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE4) (a := (rep6AE 4).1) (b := (rep6AE 4).2)
    (val := val6AE4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE5) (a := (rep6AE 5).1) (b := (rep6AE 5).2)
    (val := val6AE5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE6) (a := (rep6AE 6).1) (b := (rep6AE 6).2)
    (val := val6AE6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE7) (a := (rep6AE 7).1) (b := (rep6AE 7).2)
    (val := val6AE7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE8) (a := (rep6AE 8).1) (b := (rep6AE 8).2)
    (val := val6AE8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE9) (a := (rep6AE 9).1) (b := (rep6AE 9).2)
    (val := val6AE9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6AE) (idx := stabIdx6AE10) (a := (rep6AE 10).1) (b := (rep6AE 10).2)
    (val := val6AE10) hP (by decide) (by decide)
  have hdec : dec6AE a b c d e f g h i j k = fun i ↦ M.op (rep6AE i).1 (rep6AE i).2 := by
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
  have key : tab6AE a b c d e f g h i j k = M.op := by
    rw [tab6AE_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AE a b c d e f g h i j k) endE06AE endX06AE = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AE j), fun j ↦ hX (x0idx6AE j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AE a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`58` monoid of `Magma.endE6AE`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AE {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AE i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AE j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AE i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AE
    (fun k ↦ (Magma.end6AE_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AE_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
