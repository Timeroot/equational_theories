import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AH` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 2 1 3)(4 5), (2 3)(4 5)⟩`

`End(M)` is `28` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `7` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(2 3)(4 5)`, `(0 1)(4 5)`, `(0 1)(2 3)`, `(0 2)(1 3)`, `(0
2 1 3)(4 5)`, `(0 3 1 2)(4 5)`, `(0 3)(1 2)`. -/
def pE6AH0 : Fin 6 → Fin 6 := id
def pE6AH1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6AH2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AH3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5
def pE6AH4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5
def pE6AH5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4
def pE6AH6 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4
def pE6AH7 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5

def permE6AH : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6AH0
  | 1 => pE6AH1
  | 2 => pE6AH2
  | 3 => pE6AH3
  | 4 => pE6AH4
  | 5 => pE6AH5
  | 6 => pE6AH6
  | 7 => pE6AH7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `28` self-maps that must be endomorphisms: `000000`, `111100`, `332210`,
`223310`, `332201`, `223301`, `000011`, `111111`, `222222`, `333322`, `110032`, `001132`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AH : Fin 28 → Fin 46656
  | 0 => 0
  | 1 => 259
  | 2 => 1821
  | 3 => 2066
  | 4 => 8301
  | 5 => 8546
  | 6 => 9072
  | 7 => 9331
  | 8 => 18662
  | 9 => 18921
  | 10 => 19447
  | 11 => 19692
  | 12 => 25927
  | 13 => 26172
  | 14 => 27734
  | 15 => 27993
  | 16 => 37324
  | 17 => 37583
  | 18 => 37640
  | 19 => 37815
  | 20 => 38130
  | 21 => 38305
  | 22 => 44115
  | 23 => 44300
  | 24 => 44605
  | 25 => 44790
  | 26 => 46396
  | _ => 46655

def endE6AH (j : Fin 28) : Fin 6 → Fin 6 := allMaps6 (eidx6AH j)

/-- Indices of the other `46628`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AH : Array Nat := #[
  0, 259, 1821, 2066, 8301, 8546, 9072, 9331, 18662, 18921, 19447, 19692, 25927, 26172, 27734,
  27993, 37324, 37583, 37640, 37815, 38130, 38305, 44115, 44300, 44605, 44790, 46396, 46655]

def xarr6AH : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AH.contains i)

def xidx6AH (j : Fin 46628) : Fin 46656 :=
  ⟨min (xarr6AH.getD j.1 0) 46655, by omega⟩

def endX6AH (j : Fin 46628) : Fin 6 → Fin 6 := allMaps6 (xidx6AH j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AH` is given. -/
def uidx6AH : Fin 8 → Fin 28
  | 0 => 25
  | 1 => 20
  | 2 => 21
  | 3 => 24
  | 4 => 23
  | 5 => 18
  | 6 => 19
  | 7 => 22

theorem permE6AH_eq_endE6AH (i : Fin 8) : permE6AH i = endE6AH (uidx6AH i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `7`, so an invariant
operation is `7` values. -/
def rep6AH : Fin 7 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (4, 0)
  | 5 => (4, 4)
  | 6 => (4, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6AH : Fin 6 → Fin 6 → Fin 7 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (2, 2)
  | 1, 3 => (2, 3)
  | 1, 4 => (3, 3)
  | 1, 5 => (3, 2)
  | 2, 0 => (2, 4)
  | 2, 1 => (2, 5)
  | 2, 2 => (0, 4)
  | 2, 3 => (1, 4)
  | 2, 4 => (3, 4)
  | 2, 5 => (3, 5)
  | 3, 0 => (2, 6)
  | 3, 1 => (2, 7)
  | 3, 2 => (1, 6)
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
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AH0 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AH0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AH1 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AH1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AH2 : Fin 1 → Fin 8
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AH3 : Fin 1 → Fin 8
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AH4 : Fin 1 → Fin 8
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `4`, `5`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AH5 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 7
def val6AH5 : Fin 2 → Fin 6
  | 0 => 4
  | 1 => 5

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `4`, `5`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AH6 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 7
def val6AH6 : Fin 2 → Fin 6
  | 0 => 4
  | 1 => 5

/-- The `7` orbit values named by the family's arguments. -/
def dec6AH (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2) : Fin 7 → Fin 6
  | 0 => val6AH0 a
  | 1 => val6AH1 b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => val6AH5 f
  | 6 => val6AH6 g

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AH_eq_transport`). -/
def tab6AH (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AH0 a
  | 0, 1 => val6AH1 b
  | 0, 2 => c
  | 0, 3 => pE6AH1 c
  | 0, 4 => d
  | 0, 5 => pE6AH1 d
  | 1, 0 => pE6AH2 (val6AH1 b)
  | 1, 1 => pE6AH2 (val6AH0 a)
  | 1, 2 => pE6AH2 c
  | 1, 3 => pE6AH3 c
  | 1, 4 => pE6AH3 d
  | 1, 5 => pE6AH2 d
  | 2, 0 => pE6AH4 c
  | 2, 1 => pE6AH5 c
  | 2, 2 => pE6AH4 (val6AH0 a)
  | 2, 3 => pE6AH4 (val6AH1 b)
  | 2, 4 => pE6AH4 d
  | 2, 5 => pE6AH5 d
  | 3, 0 => pE6AH6 c
  | 3, 1 => pE6AH7 c
  | 3, 2 => pE6AH6 (val6AH1 b)
  | 3, 3 => pE6AH6 (val6AH0 a)
  | 3, 4 => pE6AH7 d
  | 3, 5 => pE6AH6 d
  | 4, 0 => e
  | 4, 1 => pE6AH3 e
  | 4, 2 => pE6AH4 e
  | 4, 3 => pE6AH7 e
  | 4, 4 => val6AH5 f
  | 4, 5 => val6AH6 g
  | 5, 0 => pE6AH1 e
  | 5, 1 => pE6AH2 e
  | 5, 2 => pE6AH5 e
  | 5, 3 => pE6AH6 e
  | 5, 4 => pE6AH1 (val6AH6 g)
  | 5, 5 => pE6AH1 (val6AH5 f)

theorem tab6AH_eq_transport (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2) :
    tab6AH a b c d e f g = Magma.transport permE6AH tr6AH (dec6AH a b c d e f g) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `3456` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AH : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AH 0 0 1 2 5 0 0
  | 1 => tab6AH 0 0 1 3 5 0 0
  | 2 => tab6AH 0 1 3 5 2 0 1
  | 3 => tab6AH 0 1 3 5 3 0 1

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6AH` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6AH : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr6AH` is addressed. -/
def encT6AH (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2) : Nat :=
  a.1 * 1728 +
    b.1 * 864 +
    c.1 * 144 +
    d.1 * 24 +
    e.1 * 4 +
    f.1 * 2 +
    g.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AH (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2) : Fin 4 :=
  ⟨min (rankArr6AH.getD (encT6AH a b c d e f g) 0) 3, by omega⟩


/-- `1` of the `28` demanded maps and `1` of the `46628` forbidden ones, enough to separate the `4`
members from the other `3452` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AH` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AH : Fin 1 → Fin 28
  | 0 => 2
def x0idx6AH : Fin 1 → Fin 46628
  | 0 => 6

def endE06AH (j : Fin 1) : Fin 6 → Fin 6 := endE6AH (e0idx6AH j)

def endX06AH (j : Fin 1) : Fin 6 → Fin 6 := endX6AH (x0idx6AH j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AH (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6AH i)

theorem end6AH_isEndo (i : Fin 4) (j : Fin 28) : (end6AH i).IsEndo (endE6AH j) := by
  revert i j; native_decide

theorem end6AH_not_isEndo (i : Fin 4) (j : Fin 46628) : ¬ (end6AH i).IsEndo (endX6AH j) := by
  revert i j; native_decide

/-- `rank6AH` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AH` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AH (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2)
    (hx : Magma.isExact (tab6AH a b c d e f g) endE06AH endX06AH = true) :
    mem6AH (rank6AH a b c d e f g) = tab6AH a b c d e f g := by
  revert hx; revert a b c d e f g; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6AH (a b : Fin 2) (c d e : Fin 6) (f g : Fin 2)
    (hx : Magma.isExact (tab6AH a b c d e f g) endE06AH endX06AH = true) :
    ∃ idx, mem6AH idx = tab6AH a b c d e f g :=
  ⟨_, mem_rank6AH a b c d e f g hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AH`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AH` turns that into a member index. -/
theorem exists_end6AH {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AH j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AH j)) : ∃ i, end6AH i = M := by
  have hP : ∀ i, M.IsEndo (permE6AH i) := by
    intro i; rw [permE6AH_eq_endE6AH]; exact hE (uidx6AH i)
  have hop : M.op = Magma.transport permE6AH tr6AH (fun i ↦ M.op (rep6AH i).1 (rep6AH i).2) :=
    Magma.op_eq_transport (rep := rep6AH) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH0) (a := (rep6AH 0).1) (b := (rep6AH 0).2)
    (val := val6AH0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH1) (a := (rep6AH 1).1) (b := (rep6AH 1).2)
    (val := val6AH1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH2) (a := (rep6AH 2).1) (b := (rep6AH 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH3) (a := (rep6AH 3).1) (b := (rep6AH 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH4) (a := (rep6AH 4).1) (b := (rep6AH 4).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH5) (a := (rep6AH 5).1) (b := (rep6AH 5).2)
    (val := val6AH5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AH) (idx := stabIdx6AH6) (a := (rep6AH 6).1) (b := (rep6AH 6).2)
    (val := val6AH6) hP (by decide) (by decide)
  have hdec : dec6AH a b c d e f g = fun i ↦ M.op (rep6AH i).1 (rep6AH i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
  have key : tab6AH a b c d e f g = M.op := by
    rw [tab6AH_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AH a b c d e f g) endE06AH endX06AH = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AH j), fun j ↦ hX (x0idx6AH j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AH a b c d e f g hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`28` monoid of `Magma.endE6AH`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AH {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AH i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AH j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AH i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AH
    (fun k ↦ (Magma.end6AH_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AH_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
