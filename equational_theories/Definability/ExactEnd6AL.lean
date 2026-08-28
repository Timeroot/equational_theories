import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AL` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(3 4 5), (0 1)(4 5)⟩`

`End(M)` is `42` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(0 1)`,
`(0 1)(4 5)`, `(0 1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`. -/
def pE6AL0 : Fin 6 → Fin 6 := id
def pE6AL1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AL2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AL3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AL4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AL5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pE6AL6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6AL7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AL8 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AL9 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AL10 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AL11 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3

def permE6AL : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6AL0
  | 1 => pE6AL1
  | 2 => pE6AL2
  | 3 => pE6AL3
  | 4 => pE6AL4
  | 5 => pE6AL5
  | 6 => pE6AL6
  | 7 => pE6AL7
  | 8 => pE6AL8
  | 9 => pE6AL9
  | 10 => pE6AL10
  | 11 => pE6AL11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `42` self-maps that must be endomorphisms: `000000`, `330000`, `440000`,
`550000`, `111111`, `331111`, `441111`, `551111`, `222222`, `332222`, `442222`, `552222`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AL : Fin 42 → Fin 46656
  | 0 => 0
  | 1 => 21
  | 2 => 28
  | 3 => 35
  | 4 => 9331
  | 5 => 9345
  | 6 => 9352
  | 7 => 9359
  | 8 => 18662
  | 9 => 18669
  | 10 => 18676
  | 11 => 18683
  | 12 => 27972
  | 13 => 27979
  | 14 => 27986
  | 15 => 27993
  | 16 => 29665
  | 17 => 29670
  | 18 => 29678
  | 19 => 30745
  | 20 => 30750
  | 21 => 30758
  | 22 => 36145
  | 23 => 36150
  | 24 => 36158
  | 25 => 37296
  | 26 => 37303
  | 27 => 37310
  | 28 => 37324
  | 29 => 38305
  | 30 => 38310
  | 31 => 38318
  | 32 => 43705
  | 33 => 43710
  | 34 => 43718
  | 35 => 44785
  | 36 => 44790
  | 37 => 44798
  | 38 => 46620
  | 39 => 46627
  | 40 => 46634
  | _ => 46655

def endE6AL (j : Fin 42) : Fin 6 → Fin 6 := allMaps6 (eidx6AL j)

/-- Indices of the other `46614`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AL : Array Nat := #[
  0, 21, 28, 35, 9331, 9345, 9352, 9359, 18662, 18669, 18676, 18683, 27972, 27979, 27986, 27993,
  29665, 29670, 29678, 30745, 30750, 30758, 36145, 36150, 36158, 37296, 37303, 37310, 37324,
  38305, 38310, 38318, 43705, 43710, 43718, 44785, 44790, 44798, 46620, 46627, 46634, 46655]

def xarr6AL : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AL.contains i)

def xidx6AL (j : Fin 46614) : Fin 46656 :=
  ⟨min (xarr6AL.getD j.1 0) 46655, by omega⟩

def endX6AL (j : Fin 46614) : Fin 6 → Fin 6 := allMaps6 (xidx6AL j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AL` is given. -/
def uidx6AL : Fin 12 → Fin 42
  | 0 => 36
  | 1 => 30
  | 2 => 33
  | 3 => 20
  | 4 => 23
  | 5 => 17
  | 6 => 35
  | 7 => 29
  | 8 => 32
  | 9 => 19
  | 10 => 22
  | 11 => 16

theorem permE6AL_eq_endE6AL (i : Fin 12) : permE6AL i = endE6AL (uidx6AL i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6AL : Fin 11 → Fin 6 × Fin 6
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
def tr6AL : Fin 6 → Fin 6 → Fin 11 × Fin 12
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
def stabIdx6AL0 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AL0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AL1 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AL1 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AL2 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AL2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AL3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AL3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AL4 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AL4 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6AL5 : Fin 12 → Fin 12
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
def val6AL5 : Fin 1 → Fin 6
  | 0 => 2

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AL6 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AL6 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AL7 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6AL7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AL8 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AL8 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AL9 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def val6AL9 : Fin 2 → Fin 6
  | 0 => 2
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AL10 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 6
def val6AL10 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6AL (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 11 → Fin 6
  | 0 => val6AL0 a
  | 1 => val6AL1 b
  | 2 => val6AL2 c
  | 3 => val6AL3 d
  | 4 => val6AL4 e
  | 5 => val6AL5 f
  | 6 => val6AL6 g
  | 7 => val6AL7 h
  | 8 => val6AL8 i
  | 9 => val6AL9 j
  | 10 => val6AL10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AL_eq_transport`). -/
def tab6AL (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4) (i j : Fin 2)
    (k : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AL0 a
  | 0, 1 => val6AL1 b
  | 0, 2 => val6AL2 c
  | 0, 3 => val6AL3 d
  | 0, 4 => pE6AL2 (val6AL3 d)
  | 0, 5 => pE6AL4 (val6AL3 d)
  | 1, 0 => pE6AL6 (val6AL1 b)
  | 1, 1 => pE6AL6 (val6AL0 a)
  | 1, 2 => pE6AL6 (val6AL2 c)
  | 1, 3 => pE6AL6 (val6AL3 d)
  | 1, 4 => pE6AL8 (val6AL3 d)
  | 1, 5 => pE6AL10 (val6AL3 d)
  | 2, 0 => val6AL4 e
  | 2, 1 => pE6AL6 (val6AL4 e)
  | 2, 2 => val6AL5 f
  | 2, 3 => val6AL6 g
  | 2, 4 => pE6AL2 (val6AL6 g)
  | 2, 5 => pE6AL4 (val6AL6 g)
  | 3, 0 => val6AL7 h
  | 3, 1 => pE6AL6 (val6AL7 h)
  | 3, 2 => val6AL8 i
  | 3, 3 => val6AL9 j
  | 3, 4 => val6AL10 k
  | 3, 5 => pE6AL1 (val6AL10 k)
  | 4, 0 => pE6AL2 (val6AL7 h)
  | 4, 1 => pE6AL8 (val6AL7 h)
  | 4, 2 => pE6AL2 (val6AL8 i)
  | 4, 3 => pE6AL2 (val6AL10 k)
  | 4, 4 => pE6AL2 (val6AL9 j)
  | 4, 5 => pE6AL3 (val6AL10 k)
  | 5, 0 => pE6AL4 (val6AL7 h)
  | 5, 1 => pE6AL10 (val6AL7 h)
  | 5, 2 => pE6AL4 (val6AL8 i)
  | 5, 3 => pE6AL4 (val6AL10 k)
  | 5, 4 => pE6AL5 (val6AL10 k)
  | 5, 5 => pE6AL4 (val6AL9 j)

theorem tab6AL_eq_transport (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4) :
    tab6AL a b c d e f g h i j k = Magma.transport permE6AL tr6AL (dec6AL a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `41472` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AL : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AL 0 0 2 3 1 0 1 0 0 1 0
  | 1 => tab6AL 0 1 1 0 2 0 0 3 1 1 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6AL` is addressed. -/
def encT6AL (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
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

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6AL` can name one
rather than search the list for it. The `41470` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6AL` excludes them. Read only by `native_decide`. -/
def rankIdx6AL : Nat → Nat
  | 4420 => 0
  | 6460 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AL (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4) : Fin 2 :=
  ⟨min (rankIdx6AL (encT6AL a b c d e f g h i j k)) 1, by omega⟩


/-- `2` of the `42` demanded maps and `3` of the `46614` forbidden ones, enough to separate the `2`
members from the other `41470` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AL` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AL : Fin 2 → Fin 42
  | 0 => 1
  | 1 => 9
def x0idx6AL : Fin 3 → Fin 46614
  | 0 => 6
  | 1 => 13
  | 2 => 104

def endE06AL (j : Fin 2) : Fin 6 → Fin 6 := endE6AL (e0idx6AL j)

def endX06AL (j : Fin 3) : Fin 6 → Fin 6 := endX6AL (x0idx6AL j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AL (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6AL i)

theorem end6AL_isEndo (i : Fin 2) (j : Fin 42) : (end6AL i).IsEndo (endE6AL j) := by
  revert i j; native_decide

theorem end6AL_not_isEndo (i : Fin 2) (j : Fin 46614) : ¬ (end6AL i).IsEndo (endX6AL j) := by
  revert i j; native_decide

/-- `rank6AL` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AL` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AL (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2) (h : Fin 4)
    (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AL a b c d e f g h i j k) endE06AL endX06AL = true) :
    mem6AL (rank6AL a b c d e f g h i j k) = tab6AL a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6AL (a b c : Fin 3) (d : Fin 4) (e : Fin 3) (f : Fin 1) (g : Fin 2)
    (h : Fin 4) (i j : Fin 2) (k : Fin 4)
    (hx : Magma.isExact (tab6AL a b c d e f g h i j k) endE06AL endX06AL = true) :
    ∃ idx, mem6AL idx = tab6AL a b c d e f g h i j k :=
  ⟨_, mem_rank6AL a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AL`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AL` turns that into a member index. -/
theorem exists_end6AL {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AL j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AL j)) : ∃ i, end6AL i = M := by
  have hP : ∀ i, M.IsEndo (permE6AL i) := by
    intro i; rw [permE6AL_eq_endE6AL]; exact hE (uidx6AL i)
  have hop : M.op = Magma.transport permE6AL tr6AL (fun i ↦ M.op (rep6AL i).1 (rep6AL i).2) :=
    Magma.op_eq_transport (rep := rep6AL) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL0) (a := (rep6AL 0).1) (b := (rep6AL 0).2)
    (val := val6AL0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL1) (a := (rep6AL 1).1) (b := (rep6AL 1).2)
    (val := val6AL1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL2) (a := (rep6AL 2).1) (b := (rep6AL 2).2)
    (val := val6AL2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL3) (a := (rep6AL 3).1) (b := (rep6AL 3).2)
    (val := val6AL3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL4) (a := (rep6AL 4).1) (b := (rep6AL 4).2)
    (val := val6AL4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL5) (a := (rep6AL 5).1) (b := (rep6AL 5).2)
    (val := val6AL5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL6) (a := (rep6AL 6).1) (b := (rep6AL 6).2)
    (val := val6AL6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL7) (a := (rep6AL 7).1) (b := (rep6AL 7).2)
    (val := val6AL7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL8) (a := (rep6AL 8).1) (b := (rep6AL 8).2)
    (val := val6AL8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL9) (a := (rep6AL 9).1) (b := (rep6AL 9).2)
    (val := val6AL9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6AL) (idx := stabIdx6AL10) (a := (rep6AL 10).1) (b := (rep6AL 10).2)
    (val := val6AL10) hP (by decide) (by decide)
  have hdec : dec6AL a b c d e f g h i j k = fun i ↦ M.op (rep6AL i).1 (rep6AL i).2 := by
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
  have key : tab6AL a b c d e f g h i j k = M.op := by
    rw [tab6AL_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AL a b c d e f g h i j k) endE06AL endX06AL = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AL j), fun j ↦ hX (x0idx6AL j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AL a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`42` monoid of `Magma.endE6AL`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AL {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AL i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AL j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AL i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AL
    (fun k ↦ (Magma.end6AL_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AL_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
