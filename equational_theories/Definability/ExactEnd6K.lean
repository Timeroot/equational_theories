import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `K` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 1)(2 3)(4 5), (0 2)(1 3)(4 5), (1 2)(4 5)⟩`

`End(M)` is `80` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `7` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(1 2)(4 5)`, `(0 1)(2 3)(4 5)`, `(0 1 3 2)`, `(0 2 3 1)`,
`(0 2)(1 3)(4 5)`, `(0 3)(4 5)`, `(0 3)(1 2)`. -/
def pE6K0 : Fin 6 → Fin 6 := id
def pE6K1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pE6K2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6K3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5
def pE6K4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5
def pE6K5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4
def pE6K6 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4
def pE6K7 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5

def permE6K : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6K0
  | 1 => pE6K1
  | 2 => pE6K2
  | 3 => pE6K3
  | 4 => pE6K4
  | 5 => pE6K5
  | 6 => pE6K6
  | 7 => pE6K7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `80` self-maps that must be endomorphisms: `330044`, `321044`, `312044`,
`303044`, `230144`, `221144`, `212144`, `203144`, `130244`, `121244`, `112244`, `103244`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6K : Fin 80 → Fin 46656
  | 0 => 36309
  | 1 => 36339
  | 2 => 36369
  | 3 => 36399
  | 4 => 36524
  | 5 => 36554
  | 6 => 36584
  | 7 => 36614
  | 8 => 36739
  | 9 => 36769
  | 10 => 36799
  | 11 => 36829
  | 12 => 36954
  | 13 => 36984
  | 14 => 37014
  | 15 => 37044
  | 16 => 37324
  | 17 => 37366
  | 18 => 37541
  | 19 => 37583
  | 20 => 37605
  | 21 => 37635
  | 22 => 37665
  | 23 => 37695
  | 24 => 37820
  | 25 => 37850
  | 26 => 37880
  | 27 => 37910
  | 28 => 38035
  | 29 => 38065
  | 30 => 38095
  | 31 => 38125
  | 32 => 38250
  | 33 => 38280
  | 34 => 38310
  | 35 => 38340
  | 36 => 38620
  | 37 => 38662
  | 38 => 38837
  | 39 => 38879
  | 40 => 44085
  | 41 => 44115
  | 42 => 44145
  | 43 => 44175
  | 44 => 44300
  | 45 => 44330
  | 46 => 44360
  | 47 => 44390
  | 48 => 44515
  | 49 => 44545
  | 50 => 44575
  | 51 => 44605
  | 52 => 44730
  | 53 => 44760
  | 54 => 44790
  | 55 => 44820
  | 56 => 45100
  | 57 => 45142
  | 58 => 45317
  | 59 => 45359
  | 60 => 45381
  | 61 => 45411
  | 62 => 45441
  | 63 => 45471
  | 64 => 45596
  | 65 => 45626
  | 66 => 45656
  | 67 => 45686
  | 68 => 45811
  | 69 => 45841
  | 70 => 45871
  | 71 => 45901
  | 72 => 46026
  | 73 => 46056
  | 74 => 46086
  | 75 => 46116
  | 76 => 46396
  | 77 => 46438
  | 78 => 46613
  | _ => 46655

def endE6K (j : Fin 80) : Fin 6 → Fin 6 := allMaps6 (eidx6K j)

/-- Indices of the other `46576`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6K : Array Nat := #[
  36309, 36339, 36369, 36399, 36524, 36554, 36584, 36614, 36739, 36769, 36799, 36829, 36954,
  36984, 37014, 37044, 37324, 37366, 37541, 37583, 37605, 37635, 37665, 37695, 37820, 37850,
  37880, 37910, 38035, 38065, 38095, 38125, 38250, 38280, 38310, 38340, 38620, 38662, 38837,
  38879, 44085, 44115, 44145, 44175, 44300, 44330, 44360, 44390, 44515, 44545, 44575, 44605,
  44730, 44760, 44790, 44820, 45100, 45142, 45317, 45359, 45381, 45411, 45441, 45471, 45596,
  45626, 45656, 45686, 45811, 45841, 45871, 45901, 46026, 46056, 46086, 46116, 46396, 46438,
  46613, 46655]

def xarr6K : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6K.contains i)

def xidx6K (j : Fin 46576) : Fin 46656 :=
  ⟨min (xarr6K.getD j.1 0) 46655, by omega⟩

def endX6K (j : Fin 46576) : Fin 6 → Fin 6 := allMaps6 (xidx6K j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6K` is given. -/
def uidx6K : Fin 8 → Fin 80
  | 0 => 54
  | 1 => 33
  | 2 => 31
  | 3 => 48
  | 4 => 47
  | 5 => 24
  | 6 => 22
  | 7 => 41

theorem permE6K_eq_endE6K (i : Fin 8) : permE6K i = endE6K (uidx6K i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `7`, so an invariant
operation is `7` values. -/
def rep6K : Fin 7 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (4, 0)
  | 5 => (4, 4)
  | 6 => (4, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6K : Fin 6 → Fin 6 → Fin 7 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (2, 2)
  | 1, 3 => (1, 3)
  | 1, 4 => (3, 3)
  | 1, 5 => (3, 2)
  | 2, 0 => (1, 4)
  | 2, 1 => (2, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (1, 5)
  | 2, 4 => (3, 4)
  | 2, 5 => (3, 5)
  | 3, 0 => (2, 6)
  | 3, 1 => (1, 6)
  | 3, 2 => (1, 7)
  | 3, 3 => (0, 6)
  | 3, 4 => (3, 7)
  | 3, 5 => (3, 6)
  | 4, 0 => (4, 0)
  | 4, 1 => (4, 3)
  | 4, 2 => (4, 4)
  | 4, 3 => (4, 7)
  | 4, 4 => (5, 0)
  | 4, 5 => (6, 0)
  | 5, 0 => (4, 1)
  | 5, 1 => (4, 2)
  | 5, 2 => (4, 5)
  | 5, 3 => (4, 6)
  | 5, 4 => (6, 1)
  | 5, 5 => (5, 1)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6K0 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6K0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6K1 : Fin 1 → Fin 8
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6K2 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6K2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6K3 : Fin 1 → Fin 8
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6K4 : Fin 1 → Fin 8
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `4`, `5`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6K5 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 7
def val6K5 : Fin 2 → Fin 6
  | 0 => 4
  | 1 => 5

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `4`, `5`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6K6 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 7
def val6K6 : Fin 2 → Fin 6
  | 0 => 4
  | 1 => 5

/-- The `7` orbit values named by the family's arguments. -/
def dec6K (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2) : Fin 7 → Fin 6
  | 0 => val6K0 a
  | 1 => b
  | 2 => val6K2 c
  | 3 => d
  | 4 => e
  | 5 => val6K5 f
  | 6 => val6K6 g

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6K_eq_transport`). -/
def tab6K (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6K0 a
  | 0, 1 => b
  | 0, 2 => pE6K1 b
  | 0, 3 => val6K2 c
  | 0, 4 => d
  | 0, 5 => pE6K1 d
  | 1, 0 => pE6K2 b
  | 1, 1 => pE6K2 (val6K0 a)
  | 1, 2 => pE6K2 (val6K2 c)
  | 1, 3 => pE6K3 b
  | 1, 4 => pE6K3 d
  | 1, 5 => pE6K2 d
  | 2, 0 => pE6K4 b
  | 2, 1 => pE6K4 (val6K2 c)
  | 2, 2 => pE6K4 (val6K0 a)
  | 2, 3 => pE6K5 b
  | 2, 4 => pE6K4 d
  | 2, 5 => pE6K5 d
  | 3, 0 => pE6K6 (val6K2 c)
  | 3, 1 => pE6K6 b
  | 3, 2 => pE6K7 b
  | 3, 3 => pE6K6 (val6K0 a)
  | 3, 4 => pE6K7 d
  | 3, 5 => pE6K6 d
  | 4, 0 => e
  | 4, 1 => pE6K3 e
  | 4, 2 => pE6K4 e
  | 4, 3 => pE6K7 e
  | 4, 4 => val6K5 f
  | 4, 5 => val6K6 g
  | 5, 0 => pE6K1 e
  | 5, 1 => pE6K2 e
  | 5, 2 => pE6K5 e
  | 5, 3 => pE6K6 e
  | 5, 4 => pE6K1 (val6K6 g)
  | 5, 5 => pE6K1 (val6K5 f)

theorem tab6K_eq_transport (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2) :
    tab6K a b c d e f g = Magma.transport permE6K tr6K (dec6K a b c d e f g) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `3456` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6K : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6K 1 2 0 4 0 0 1
  | 1 => tab6K 1 3 1 0 4 0 0

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6K` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6K : Array Nat := #[
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
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr6K` is addressed. -/
def encT6K (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2) : Nat :=
  a.1 * 1728 +
    b.1 * 288 +
    c.1 * 144 +
    d.1 * 24 +
    e.1 * 4 +
    f.1 * 2 +
    g.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6K (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2) : Fin 2 :=
  ⟨min (rankArr6K.getD (encT6K a b c d e f g) 0) 1, by omega⟩


/-- `2` of the `80` demanded maps and `2` of the `46576` forbidden ones, enough to separate the `2`
members from the other `3454` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6K` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6K : Fin 2 → Fin 80
  | 0 => 0
  | 1 => 37
def x0idx6K : Fin 2 → Fin 46576
  | 0 => 0
  | 1 => 36455

def endE06K (j : Fin 2) : Fin 6 → Fin 6 := endE6K (e0idx6K j)

def endX06K (j : Fin 2) : Fin 6 → Fin 6 := endX6K (x0idx6K j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6K (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6K i)

theorem end6K_isEndo (i : Fin 2) (j : Fin 80) : (end6K i).IsEndo (endE6K j) := by
  revert i j; native_decide

theorem end6K_not_isEndo (i : Fin 2) (j : Fin 46576) : ¬ (end6K i).IsEndo (endX6K j) := by
  revert i j; native_decide

/-- `rank6K` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6K` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6K (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2)
    (hx : Magma.isExact (tab6K a b c d e f g) endE06K endX06K = true) :
    mem6K (rank6K a b c d e f g) = tab6K a b c d e f g := by
  revert hx; revert a b c d e f g; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6K (a : Fin 2) (b : Fin 6) (c : Fin 2) (d e : Fin 6) (f g : Fin 2)
    (hx : Magma.isExact (tab6K a b c d e f g) endE06K endX06K = true) :
    ∃ idx, mem6K idx = tab6K a b c d e f g :=
  ⟨_, mem_rank6K a b c d e f g hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6K`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6K` turns that into a member index. -/
theorem exists_end6K {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6K j))
    (hX : ∀ j, ¬ M.IsEndo (endX6K j)) : ∃ i, end6K i = M := by
  have hP : ∀ i, M.IsEndo (permE6K i) := by
    intro i; rw [permE6K_eq_endE6K]; exact hE (uidx6K i)
  have hop : M.op = Magma.transport permE6K tr6K (fun i ↦ M.op (rep6K i).1 (rep6K i).2) :=
    Magma.op_eq_transport (rep := rep6K) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K0) (a := (rep6K 0).1) (b := (rep6K 0).2)
    (val := val6K0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K1) (a := (rep6K 1).1) (b := (rep6K 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K2) (a := (rep6K 2).1) (b := (rep6K 2).2)
    (val := val6K2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K3) (a := (rep6K 3).1) (b := (rep6K 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K4) (a := (rep6K 4).1) (b := (rep6K 4).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K5) (a := (rep6K 5).1) (b := (rep6K 5).2)
    (val := val6K5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6K) (idx := stabIdx6K6) (a := (rep6K 6).1) (b := (rep6K 6).2)
    (val := val6K6) hP (by decide) (by decide)
  have hdec : dec6K a b c d e f g = fun i ↦ M.op (rep6K i).1 (rep6K i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
  have key : tab6K a b c d e f g = M.op := by
    rw [tab6K_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6K a b c d e f g) endE06K endX06K = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6K j), fun j ↦ hX (x0idx6K j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6K a b c d e f g hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`80` monoid of `Magma.endE6K`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6K {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6K i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6K j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6K i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6K
    (fun k ↦ (Magma.end6K_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6K_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
