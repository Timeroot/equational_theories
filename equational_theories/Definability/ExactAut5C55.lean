import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `C55` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`5` group `⟨(0 1 2 4 3)⟩` -/

/-- The `5` elements of the group: `()`, `(0 1 2 4 3)`, `(0 2 3 1 4)`, `(0 3 4 2 1)`, `(0 4 1 3 2)`.
-/
def pEC550 : Fin 5 → Fin 5 := id
def pEC551 : Fin 5 → Fin 5 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3
def pEC552 : Fin 5 → Fin 5 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0
def pEC553 : Fin 5 → Fin 5 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2
def pEC554 : Fin 5 → Fin 5 | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1

def permEC55 : Fin 5 → Fin 5 → Fin 5
  | 0 => pEC550
  | 1 => pEC551
  | 2 => pEC552
  | 3 => pEC553
  | 4 => pEC554

def permEinvC55 : Fin 5 → Fin 5 → Fin 5
  | 0 => pEC550
  | 1 => pEC553
  | 2 => pEC554
  | 3 => pEC551
  | 4 => pEC552

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEC55 (i : Fin 5) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permEC55 i) (permEinvC55 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 1)(2 3)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXC550 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4
def pXC550inv : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4

def permXC55 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXC550

def permXinvC55 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXC550inv

def eXC55 (i : Fin 1) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXC55 i) (permXinvC55 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `5`, so an invariant
operation is `5` values. -/
def repC55 : Fin 5 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)
  | 4 => (0, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trC55 : Fin 5 → Fin 5 → Fin 5 × Fin 5
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (4, 0)
  | 1, 0 => (3, 1)
  | 1, 1 => (0, 1)
  | 1, 2 => (1, 1)
  | 1, 3 => (4, 1)
  | 1, 4 => (2, 1)
  | 2, 0 => (4, 2)
  | 2, 1 => (3, 2)
  | 2, 2 => (0, 2)
  | 2, 3 => (2, 2)
  | 2, 4 => (1, 2)
  | 3, 0 => (1, 3)
  | 3, 1 => (2, 3)
  | 3, 2 => (4, 3)
  | 3, 3 => (0, 3)
  | 3, 4 => (3, 3)
  | 4, 0 => (2, 4)
  | 4, 1 => (4, 4)
  | 4, 2 => (3, 4)
  | 4, 3 => (1, 4)
  | 4, 4 => (0, 4)

/-- The one group element fixing both coordinates of orbit `0`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxC550 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxC551 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxC552 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxC553 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxC554 : Fin 1 → Fin 5
  | 0 => 0

/-- The `5` orbit values named by the family's arguments. -/
def decC55 (a b c d e : Fin 5) : Fin 5 → Fin 5
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabC55_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabC55 (a b c d e : Fin 5) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => d
  | 0, 4 => e
  | 1, 0 => pEC551 d
  | 1, 1 => pEC551 a
  | 1, 2 => pEC551 b
  | 1, 3 => pEC551 e
  | 1, 4 => pEC551 c
  | 2, 0 => pEC552 e
  | 2, 1 => pEC552 d
  | 2, 2 => pEC552 a
  | 2, 3 => pEC552 c
  | 2, 4 => pEC552 b
  | 3, 0 => pEC553 b
  | 3, 1 => pEC553 c
  | 3, 2 => pEC553 e
  | 3, 3 => pEC553 a
  | 3, 4 => pEC553 d
  | 4, 0 => pEC554 c
  | 4, 1 => pEC554 e
  | 4, 2 => pEC554 d
  | 4, 3 => pEC554 b
  | 4, 4 => pEC554 a

theorem tabC55_eq_transport (a b c d e : Fin 5) :
    tabC55 a b c d e = Magma.transport permEC55 trC55 (decC55 a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `3100` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `3125` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowC550 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 0 0 0 1
  | 1 => tabC55 0 0 0 0 2
  | 2 => tabC55 0 0 0 0 3
  | 3 => tabC55 0 0 0 0 4
  | 4 => tabC55 0 0 0 1 0
  | 5 => tabC55 0 0 0 1 1
  | 6 => tabC55 0 0 0 1 2
  | 7 => tabC55 0 0 0 1 3
  | 8 => tabC55 0 0 0 1 4
  | 9 => tabC55 0 0 0 2 0
  | 10 => tabC55 0 0 0 2 1
  | 11 => tabC55 0 0 0 2 2
  | 12 => tabC55 0 0 0 2 3
  | 13 => tabC55 0 0 0 2 4
  | 14 => tabC55 0 0 0 3 0
  | 15 => tabC55 0 0 0 3 1
  | 16 => tabC55 0 0 0 3 2
  | 17 => tabC55 0 0 0 3 3
  | 18 => tabC55 0 0 0 3 4
  | 19 => tabC55 0 0 0 4 0
  | 20 => tabC55 0 0 0 4 1
  | 21 => tabC55 0 0 0 4 2
  | 22 => tabC55 0 0 0 4 3
  | 23 => tabC55 0 0 0 4 4
  | 24 => tabC55 0 0 1 0 0
  | 25 => tabC55 0 0 1 0 1
  | 26 => tabC55 0 0 1 0 2
  | 27 => tabC55 0 0 1 0 4
  | 28 => tabC55 0 0 1 1 0
  | 29 => tabC55 0 0 1 1 1
  | 30 => tabC55 0 0 1 1 2
  | 31 => tabC55 0 0 1 1 3
  | 32 => tabC55 0 0 1 1 4
  | 33 => tabC55 0 0 1 2 0
  | 34 => tabC55 0 0 1 2 1
  | 35 => tabC55 0 0 1 2 2
  | 36 => tabC55 0 0 1 2 3
  | 37 => tabC55 0 0 1 2 4
  | 38 => tabC55 0 0 1 3 0
  | 39 => tabC55 0 0 1 3 1
  | 40 => tabC55 0 0 1 3 2
  | 41 => tabC55 0 0 1 3 3
  | 42 => tabC55 0 0 1 3 4
  | 43 => tabC55 0 0 1 4 0
  | 44 => tabC55 0 0 1 4 1
  | 45 => tabC55 0 0 1 4 2
  | 46 => tabC55 0 0 1 4 3
  | 47 => tabC55 0 0 1 4 4
  | 48 => tabC55 0 0 2 0 0
  | 49 => tabC55 0 0 2 0 1
  | 50 => tabC55 0 0 2 0 2
  | 51 => tabC55 0 0 2 0 3
  | 52 => tabC55 0 0 2 1 0
  | 53 => tabC55 0 0 2 1 1
  | 54 => tabC55 0 0 2 1 2
  | _ => tabC55 0 0 2 1 3
def memRowC551 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 0 2 1 4
  | 1 => tabC55 0 0 2 2 0
  | 2 => tabC55 0 0 2 2 1
  | 3 => tabC55 0 0 2 2 2
  | 4 => tabC55 0 0 2 2 3
  | 5 => tabC55 0 0 2 2 4
  | 6 => tabC55 0 0 2 3 0
  | 7 => tabC55 0 0 2 3 1
  | 8 => tabC55 0 0 2 3 2
  | 9 => tabC55 0 0 2 3 3
  | 10 => tabC55 0 0 2 3 4
  | 11 => tabC55 0 0 2 4 0
  | 12 => tabC55 0 0 2 4 1
  | 13 => tabC55 0 0 2 4 2
  | 14 => tabC55 0 0 2 4 3
  | 15 => tabC55 0 0 2 4 4
  | 16 => tabC55 0 0 3 0 0
  | 17 => tabC55 0 0 3 0 2
  | 18 => tabC55 0 0 3 0 3
  | 19 => tabC55 0 0 3 0 4
  | 20 => tabC55 0 0 3 1 0
  | 21 => tabC55 0 0 3 1 1
  | 22 => tabC55 0 0 3 1 2
  | 23 => tabC55 0 0 3 1 3
  | 24 => tabC55 0 0 3 1 4
  | 25 => tabC55 0 0 3 2 0
  | 26 => tabC55 0 0 3 2 1
  | 27 => tabC55 0 0 3 2 2
  | 28 => tabC55 0 0 3 2 3
  | 29 => tabC55 0 0 3 2 4
  | 30 => tabC55 0 0 3 3 0
  | 31 => tabC55 0 0 3 3 1
  | 32 => tabC55 0 0 3 3 2
  | 33 => tabC55 0 0 3 3 3
  | 34 => tabC55 0 0 3 3 4
  | 35 => tabC55 0 0 3 4 0
  | 36 => tabC55 0 0 3 4 1
  | 37 => tabC55 0 0 3 4 2
  | 38 => tabC55 0 0 3 4 3
  | 39 => tabC55 0 0 3 4 4
  | 40 => tabC55 0 0 4 0 0
  | 41 => tabC55 0 0 4 0 1
  | 42 => tabC55 0 0 4 0 3
  | 43 => tabC55 0 0 4 0 4
  | 44 => tabC55 0 0 4 1 0
  | 45 => tabC55 0 0 4 1 1
  | 46 => tabC55 0 0 4 1 2
  | 47 => tabC55 0 0 4 1 3
  | 48 => tabC55 0 0 4 1 4
  | 49 => tabC55 0 0 4 2 0
  | 50 => tabC55 0 0 4 2 1
  | 51 => tabC55 0 0 4 2 2
  | 52 => tabC55 0 0 4 2 3
  | 53 => tabC55 0 0 4 2 4
  | 54 => tabC55 0 0 4 3 0
  | _ => tabC55 0 0 4 3 1
def memRowC552 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 0 4 3 2
  | 1 => tabC55 0 0 4 3 3
  | 2 => tabC55 0 0 4 3 4
  | 3 => tabC55 0 0 4 4 0
  | 4 => tabC55 0 0 4 4 1
  | 5 => tabC55 0 0 4 4 2
  | 6 => tabC55 0 0 4 4 3
  | 7 => tabC55 0 0 4 4 4
  | 8 => tabC55 0 1 0 0 0
  | 9 => tabC55 0 1 0 0 1
  | 10 => tabC55 0 1 0 0 2
  | 11 => tabC55 0 1 0 0 3
  | 12 => tabC55 0 1 0 0 4
  | 13 => tabC55 0 1 0 1 0
  | 14 => tabC55 0 1 0 1 1
  | 15 => tabC55 0 1 0 1 2
  | 16 => tabC55 0 1 0 1 3
  | 17 => tabC55 0 1 0 1 4
  | 18 => tabC55 0 1 0 2 0
  | 19 => tabC55 0 1 0 2 1
  | 20 => tabC55 0 1 0 2 2
  | 21 => tabC55 0 1 0 2 3
  | 22 => tabC55 0 1 0 2 4
  | 23 => tabC55 0 1 0 3 1
  | 24 => tabC55 0 1 0 3 2
  | 25 => tabC55 0 1 0 3 3
  | 26 => tabC55 0 1 0 3 4
  | 27 => tabC55 0 1 0 4 0
  | 28 => tabC55 0 1 0 4 1
  | 29 => tabC55 0 1 0 4 2
  | 30 => tabC55 0 1 0 4 3
  | 31 => tabC55 0 1 0 4 4
  | 32 => tabC55 0 1 1 0 0
  | 33 => tabC55 0 1 1 0 1
  | 34 => tabC55 0 1 1 0 2
  | 35 => tabC55 0 1 1 0 3
  | 36 => tabC55 0 1 1 0 4
  | 37 => tabC55 0 1 1 1 0
  | 38 => tabC55 0 1 1 1 1
  | 39 => tabC55 0 1 1 1 2
  | 40 => tabC55 0 1 1 1 3
  | 41 => tabC55 0 1 1 1 4
  | 42 => tabC55 0 1 1 2 0
  | 43 => tabC55 0 1 1 2 1
  | 44 => tabC55 0 1 1 2 2
  | 45 => tabC55 0 1 1 2 3
  | 46 => tabC55 0 1 1 2 4
  | 47 => tabC55 0 1 1 3 0
  | 48 => tabC55 0 1 1 3 1
  | 49 => tabC55 0 1 1 3 2
  | 50 => tabC55 0 1 1 3 4
  | 51 => tabC55 0 1 1 4 0
  | 52 => tabC55 0 1 1 4 1
  | 53 => tabC55 0 1 1 4 2
  | 54 => tabC55 0 1 1 4 3
  | _ => tabC55 0 1 1 4 4
def memRowC553 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 1 2 0 0
  | 1 => tabC55 0 1 2 0 1
  | 2 => tabC55 0 1 2 0 2
  | 3 => tabC55 0 1 2 0 3
  | 4 => tabC55 0 1 2 0 4
  | 5 => tabC55 0 1 2 1 0
  | 6 => tabC55 0 1 2 1 1
  | 7 => tabC55 0 1 2 1 2
  | 8 => tabC55 0 1 2 1 3
  | 9 => tabC55 0 1 2 1 4
  | 10 => tabC55 0 1 2 2 0
  | 11 => tabC55 0 1 2 2 1
  | 12 => tabC55 0 1 2 2 2
  | 13 => tabC55 0 1 2 2 3
  | 14 => tabC55 0 1 2 2 4
  | 15 => tabC55 0 1 2 3 0
  | 16 => tabC55 0 1 2 3 1
  | 17 => tabC55 0 1 2 3 2
  | 18 => tabC55 0 1 2 3 3
  | 19 => tabC55 0 1 2 4 0
  | 20 => tabC55 0 1 2 4 1
  | 21 => tabC55 0 1 2 4 2
  | 22 => tabC55 0 1 2 4 3
  | 23 => tabC55 0 1 2 4 4
  | 24 => tabC55 0 1 3 0 0
  | 25 => tabC55 0 1 3 0 1
  | 26 => tabC55 0 1 3 0 2
  | 27 => tabC55 0 1 3 0 3
  | 28 => tabC55 0 1 3 0 4
  | 29 => tabC55 0 1 3 1 0
  | 30 => tabC55 0 1 3 1 1
  | 31 => tabC55 0 1 3 1 2
  | 32 => tabC55 0 1 3 1 3
  | 33 => tabC55 0 1 3 1 4
  | 34 => tabC55 0 1 3 2 0
  | 35 => tabC55 0 1 3 2 1
  | 36 => tabC55 0 1 3 2 2
  | 37 => tabC55 0 1 3 2 3
  | 38 => tabC55 0 1 3 2 4
  | 39 => tabC55 0 1 3 3 0
  | 40 => tabC55 0 1 3 3 2
  | 41 => tabC55 0 1 3 3 3
  | 42 => tabC55 0 1 3 3 4
  | 43 => tabC55 0 1 3 4 0
  | 44 => tabC55 0 1 3 4 1
  | 45 => tabC55 0 1 3 4 2
  | 46 => tabC55 0 1 3 4 3
  | 47 => tabC55 0 1 3 4 4
  | 48 => tabC55 0 1 4 0 0
  | 49 => tabC55 0 1 4 0 1
  | 50 => tabC55 0 1 4 0 2
  | 51 => tabC55 0 1 4 0 3
  | 52 => tabC55 0 1 4 0 4
  | 53 => tabC55 0 1 4 1 0
  | 54 => tabC55 0 1 4 1 1
  | _ => tabC55 0 1 4 1 2
def memRowC554 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 1 4 1 3
  | 1 => tabC55 0 1 4 1 4
  | 2 => tabC55 0 1 4 2 0
  | 3 => tabC55 0 1 4 2 1
  | 4 => tabC55 0 1 4 2 2
  | 5 => tabC55 0 1 4 2 3
  | 6 => tabC55 0 1 4 2 4
  | 7 => tabC55 0 1 4 3 0
  | 8 => tabC55 0 1 4 3 1
  | 9 => tabC55 0 1 4 3 3
  | 10 => tabC55 0 1 4 3 4
  | 11 => tabC55 0 1 4 4 0
  | 12 => tabC55 0 1 4 4 1
  | 13 => tabC55 0 1 4 4 2
  | 14 => tabC55 0 1 4 4 3
  | 15 => tabC55 0 1 4 4 4
  | 16 => tabC55 0 2 0 0 0
  | 17 => tabC55 0 2 0 0 1
  | 18 => tabC55 0 2 0 0 2
  | 19 => tabC55 0 2 0 0 3
  | 20 => tabC55 0 2 0 0 4
  | 21 => tabC55 0 2 0 1 0
  | 22 => tabC55 0 2 0 1 1
  | 23 => tabC55 0 2 0 1 2
  | 24 => tabC55 0 2 0 1 3
  | 25 => tabC55 0 2 0 1 4
  | 26 => tabC55 0 2 0 2 0
  | 27 => tabC55 0 2 0 2 1
  | 28 => tabC55 0 2 0 2 2
  | 29 => tabC55 0 2 0 2 3
  | 30 => tabC55 0 2 0 2 4
  | 31 => tabC55 0 2 0 3 0
  | 32 => tabC55 0 2 0 3 1
  | 33 => tabC55 0 2 0 3 2
  | 34 => tabC55 0 2 0 3 3
  | 35 => tabC55 0 2 0 3 4
  | 36 => tabC55 0 2 0 4 1
  | 37 => tabC55 0 2 0 4 2
  | 38 => tabC55 0 2 0 4 3
  | 39 => tabC55 0 2 0 4 4
  | 40 => tabC55 0 2 1 0 0
  | 41 => tabC55 0 2 1 0 1
  | 42 => tabC55 0 2 1 0 2
  | 43 => tabC55 0 2 1 0 3
  | 44 => tabC55 0 2 1 0 4
  | 45 => tabC55 0 2 1 1 0
  | 46 => tabC55 0 2 1 1 1
  | 47 => tabC55 0 2 1 1 2
  | 48 => tabC55 0 2 1 1 3
  | 49 => tabC55 0 2 1 1 4
  | 50 => tabC55 0 2 1 2 0
  | 51 => tabC55 0 2 1 2 1
  | 52 => tabC55 0 2 1 2 2
  | 53 => tabC55 0 2 1 2 3
  | 54 => tabC55 0 2 1 2 4
  | _ => tabC55 0 2 1 3 0
def memRowC555 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 2 1 3 1
  | 1 => tabC55 0 2 1 3 2
  | 2 => tabC55 0 2 1 3 3
  | 3 => tabC55 0 2 1 3 4
  | 4 => tabC55 0 2 1 4 0
  | 5 => tabC55 0 2 1 4 1
  | 6 => tabC55 0 2 1 4 2
  | 7 => tabC55 0 2 1 4 4
  | 8 => tabC55 0 2 2 0 0
  | 9 => tabC55 0 2 2 0 1
  | 10 => tabC55 0 2 2 0 2
  | 11 => tabC55 0 2 2 0 3
  | 12 => tabC55 0 2 2 0 4
  | 13 => tabC55 0 2 2 1 0
  | 14 => tabC55 0 2 2 1 1
  | 15 => tabC55 0 2 2 1 2
  | 16 => tabC55 0 2 2 1 3
  | 17 => tabC55 0 2 2 1 4
  | 18 => tabC55 0 2 2 2 0
  | 19 => tabC55 0 2 2 2 1
  | 20 => tabC55 0 2 2 2 2
  | 21 => tabC55 0 2 2 2 3
  | 22 => tabC55 0 2 2 2 4
  | 23 => tabC55 0 2 2 3 0
  | 24 => tabC55 0 2 2 3 1
  | 25 => tabC55 0 2 2 3 2
  | 26 => tabC55 0 2 2 3 3
  | 27 => tabC55 0 2 2 3 4
  | 28 => tabC55 0 2 2 4 0
  | 29 => tabC55 0 2 2 4 1
  | 30 => tabC55 0 2 2 4 2
  | 31 => tabC55 0 2 2 4 3
  | 32 => tabC55 0 2 3 0 0
  | 33 => tabC55 0 2 3 0 1
  | 34 => tabC55 0 2 3 0 2
  | 35 => tabC55 0 2 3 0 3
  | 36 => tabC55 0 2 3 0 4
  | 37 => tabC55 0 2 3 1 0
  | 38 => tabC55 0 2 3 1 1
  | 39 => tabC55 0 2 3 1 2
  | 40 => tabC55 0 2 3 1 3
  | 41 => tabC55 0 2 3 1 4
  | 42 => tabC55 0 2 3 2 0
  | 43 => tabC55 0 2 3 2 1
  | 44 => tabC55 0 2 3 2 2
  | 45 => tabC55 0 2 3 2 3
  | 46 => tabC55 0 2 3 2 4
  | 47 => tabC55 0 2 3 3 0
  | 48 => tabC55 0 2 3 3 1
  | 49 => tabC55 0 2 3 3 2
  | 50 => tabC55 0 2 3 3 3
  | 51 => tabC55 0 2 3 3 4
  | 52 => tabC55 0 2 3 4 0
  | 53 => tabC55 0 2 3 4 2
  | 54 => tabC55 0 2 3 4 3
  | _ => tabC55 0 2 3 4 4
def memRowC556 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 2 4 0 0
  | 1 => tabC55 0 2 4 0 1
  | 2 => tabC55 0 2 4 0 2
  | 3 => tabC55 0 2 4 0 3
  | 4 => tabC55 0 2 4 0 4
  | 5 => tabC55 0 2 4 1 0
  | 6 => tabC55 0 2 4 1 1
  | 7 => tabC55 0 2 4 1 2
  | 8 => tabC55 0 2 4 1 3
  | 9 => tabC55 0 2 4 1 4
  | 10 => tabC55 0 2 4 2 0
  | 11 => tabC55 0 2 4 2 1
  | 12 => tabC55 0 2 4 2 2
  | 13 => tabC55 0 2 4 2 3
  | 14 => tabC55 0 2 4 2 4
  | 15 => tabC55 0 2 4 3 0
  | 16 => tabC55 0 2 4 3 1
  | 17 => tabC55 0 2 4 3 2
  | 18 => tabC55 0 2 4 3 3
  | 19 => tabC55 0 2 4 3 4
  | 20 => tabC55 0 2 4 4 0
  | 21 => tabC55 0 2 4 4 1
  | 22 => tabC55 0 2 4 4 3
  | 23 => tabC55 0 2 4 4 4
  | 24 => tabC55 0 3 0 0 0
  | 25 => tabC55 0 3 0 0 1
  | 26 => tabC55 0 3 0 0 2
  | 27 => tabC55 0 3 0 0 3
  | 28 => tabC55 0 3 0 0 4
  | 29 => tabC55 0 3 0 1 1
  | 30 => tabC55 0 3 0 1 2
  | 31 => tabC55 0 3 0 1 3
  | 32 => tabC55 0 3 0 1 4
  | 33 => tabC55 0 3 0 2 0
  | 34 => tabC55 0 3 0 2 1
  | 35 => tabC55 0 3 0 2 2
  | 36 => tabC55 0 3 0 2 3
  | 37 => tabC55 0 3 0 2 4
  | 38 => tabC55 0 3 0 3 0
  | 39 => tabC55 0 3 0 3 1
  | 40 => tabC55 0 3 0 3 2
  | 41 => tabC55 0 3 0 3 3
  | 42 => tabC55 0 3 0 3 4
  | 43 => tabC55 0 3 0 4 0
  | 44 => tabC55 0 3 0 4 1
  | 45 => tabC55 0 3 0 4 2
  | 46 => tabC55 0 3 0 4 3
  | 47 => tabC55 0 3 0 4 4
  | 48 => tabC55 0 3 1 0 0
  | 49 => tabC55 0 3 1 0 1
  | 50 => tabC55 0 3 1 0 2
  | 51 => tabC55 0 3 1 0 3
  | 52 => tabC55 0 3 1 0 4
  | 53 => tabC55 0 3 1 1 0
  | 54 => tabC55 0 3 1 1 1
  | _ => tabC55 0 3 1 1 2
def memRowC557 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 3 1 1 4
  | 1 => tabC55 0 3 1 2 0
  | 2 => tabC55 0 3 1 2 1
  | 3 => tabC55 0 3 1 2 2
  | 4 => tabC55 0 3 1 2 3
  | 5 => tabC55 0 3 1 2 4
  | 6 => tabC55 0 3 1 3 0
  | 7 => tabC55 0 3 1 3 1
  | 8 => tabC55 0 3 1 3 2
  | 9 => tabC55 0 3 1 3 3
  | 10 => tabC55 0 3 1 3 4
  | 11 => tabC55 0 3 1 4 0
  | 12 => tabC55 0 3 1 4 1
  | 13 => tabC55 0 3 1 4 2
  | 14 => tabC55 0 3 1 4 3
  | 15 => tabC55 0 3 1 4 4
  | 16 => tabC55 0 3 2 0 0
  | 17 => tabC55 0 3 2 0 1
  | 18 => tabC55 0 3 2 0 2
  | 19 => tabC55 0 3 2 0 3
  | 20 => tabC55 0 3 2 0 4
  | 21 => tabC55 0 3 2 1 0
  | 22 => tabC55 0 3 2 1 1
  | 23 => tabC55 0 3 2 1 2
  | 24 => tabC55 0 3 2 1 3
  | 25 => tabC55 0 3 2 2 0
  | 26 => tabC55 0 3 2 2 1
  | 27 => tabC55 0 3 2 2 2
  | 28 => tabC55 0 3 2 2 3
  | 29 => tabC55 0 3 2 2 4
  | 30 => tabC55 0 3 2 3 0
  | 31 => tabC55 0 3 2 3 1
  | 32 => tabC55 0 3 2 3 2
  | 33 => tabC55 0 3 2 3 3
  | 34 => tabC55 0 3 2 3 4
  | 35 => tabC55 0 3 2 4 0
  | 36 => tabC55 0 3 2 4 1
  | 37 => tabC55 0 3 2 4 2
  | 38 => tabC55 0 3 2 4 3
  | 39 => tabC55 0 3 2 4 4
  | 40 => tabC55 0 3 3 0 0
  | 41 => tabC55 0 3 3 0 1
  | 42 => tabC55 0 3 3 0 2
  | 43 => tabC55 0 3 3 0 3
  | 44 => tabC55 0 3 3 0 4
  | 45 => tabC55 0 3 3 1 0
  | 46 => tabC55 0 3 3 1 2
  | 47 => tabC55 0 3 3 1 3
  | 48 => tabC55 0 3 3 1 4
  | 49 => tabC55 0 3 3 2 0
  | 50 => tabC55 0 3 3 2 1
  | 51 => tabC55 0 3 3 2 2
  | 52 => tabC55 0 3 3 2 3
  | 53 => tabC55 0 3 3 2 4
  | 54 => tabC55 0 3 3 3 0
  | _ => tabC55 0 3 3 3 1
def memRowC558 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 3 3 3 2
  | 1 => tabC55 0 3 3 3 3
  | 2 => tabC55 0 3 3 3 4
  | 3 => tabC55 0 3 3 4 0
  | 4 => tabC55 0 3 3 4 1
  | 5 => tabC55 0 3 3 4 2
  | 6 => tabC55 0 3 3 4 3
  | 7 => tabC55 0 3 3 4 4
  | 8 => tabC55 0 3 4 0 0
  | 9 => tabC55 0 3 4 0 1
  | 10 => tabC55 0 3 4 0 2
  | 11 => tabC55 0 3 4 0 3
  | 12 => tabC55 0 3 4 0 4
  | 13 => tabC55 0 3 4 1 0
  | 14 => tabC55 0 3 4 1 1
  | 15 => tabC55 0 3 4 1 3
  | 16 => tabC55 0 3 4 1 4
  | 17 => tabC55 0 3 4 2 0
  | 18 => tabC55 0 3 4 2 1
  | 19 => tabC55 0 3 4 2 2
  | 20 => tabC55 0 3 4 2 3
  | 21 => tabC55 0 3 4 2 4
  | 22 => tabC55 0 3 4 3 0
  | 23 => tabC55 0 3 4 3 1
  | 24 => tabC55 0 3 4 3 2
  | 25 => tabC55 0 3 4 3 3
  | 26 => tabC55 0 3 4 3 4
  | 27 => tabC55 0 3 4 4 0
  | 28 => tabC55 0 3 4 4 1
  | 29 => tabC55 0 3 4 4 2
  | 30 => tabC55 0 3 4 4 3
  | 31 => tabC55 0 3 4 4 4
  | 32 => tabC55 0 4 0 0 0
  | 33 => tabC55 0 4 0 0 1
  | 34 => tabC55 0 4 0 0 2
  | 35 => tabC55 0 4 0 0 3
  | 36 => tabC55 0 4 0 0 4
  | 37 => tabC55 0 4 0 1 0
  | 38 => tabC55 0 4 0 1 1
  | 39 => tabC55 0 4 0 1 2
  | 40 => tabC55 0 4 0 1 3
  | 41 => tabC55 0 4 0 1 4
  | 42 => tabC55 0 4 0 2 1
  | 43 => tabC55 0 4 0 2 2
  | 44 => tabC55 0 4 0 2 3
  | 45 => tabC55 0 4 0 2 4
  | 46 => tabC55 0 4 0 3 0
  | 47 => tabC55 0 4 0 3 1
  | 48 => tabC55 0 4 0 3 2
  | 49 => tabC55 0 4 0 3 3
  | 50 => tabC55 0 4 0 3 4
  | 51 => tabC55 0 4 0 4 0
  | 52 => tabC55 0 4 0 4 1
  | 53 => tabC55 0 4 0 4 2
  | 54 => tabC55 0 4 0 4 3
  | _ => tabC55 0 4 0 4 4
def memRowC559 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 4 1 0 0
  | 1 => tabC55 0 4 1 0 1
  | 2 => tabC55 0 4 1 0 2
  | 3 => tabC55 0 4 1 0 3
  | 4 => tabC55 0 4 1 0 4
  | 5 => tabC55 0 4 1 1 0
  | 6 => tabC55 0 4 1 1 1
  | 7 => tabC55 0 4 1 1 2
  | 8 => tabC55 0 4 1 1 3
  | 9 => tabC55 0 4 1 1 4
  | 10 => tabC55 0 4 1 2 0
  | 11 => tabC55 0 4 1 2 1
  | 12 => tabC55 0 4 1 2 2
  | 13 => tabC55 0 4 1 2 4
  | 14 => tabC55 0 4 1 3 0
  | 15 => tabC55 0 4 1 3 1
  | 16 => tabC55 0 4 1 3 2
  | 17 => tabC55 0 4 1 3 3
  | 18 => tabC55 0 4 1 3 4
  | 19 => tabC55 0 4 1 4 0
  | 20 => tabC55 0 4 1 4 1
  | 21 => tabC55 0 4 1 4 2
  | 22 => tabC55 0 4 1 4 3
  | 23 => tabC55 0 4 1 4 4
  | 24 => tabC55 0 4 2 0 0
  | 25 => tabC55 0 4 2 0 1
  | 26 => tabC55 0 4 2 0 2
  | 27 => tabC55 0 4 2 0 3
  | 28 => tabC55 0 4 2 0 4
  | 29 => tabC55 0 4 2 1 0
  | 30 => tabC55 0 4 2 1 1
  | 31 => tabC55 0 4 2 1 2
  | 32 => tabC55 0 4 2 1 3
  | 33 => tabC55 0 4 2 1 4
  | 34 => tabC55 0 4 2 2 0
  | 35 => tabC55 0 4 2 2 1
  | 36 => tabC55 0 4 2 2 2
  | 37 => tabC55 0 4 2 2 3
  | 38 => tabC55 0 4 2 3 0
  | 39 => tabC55 0 4 2 3 1
  | 40 => tabC55 0 4 2 3 2
  | 41 => tabC55 0 4 2 3 3
  | 42 => tabC55 0 4 2 3 4
  | 43 => tabC55 0 4 2 4 0
  | 44 => tabC55 0 4 2 4 1
  | 45 => tabC55 0 4 2 4 2
  | 46 => tabC55 0 4 2 4 3
  | 47 => tabC55 0 4 2 4 4
  | 48 => tabC55 0 4 3 0 0
  | 49 => tabC55 0 4 3 0 1
  | 50 => tabC55 0 4 3 0 2
  | 51 => tabC55 0 4 3 0 3
  | 52 => tabC55 0 4 3 0 4
  | 53 => tabC55 0 4 3 1 0
  | 54 => tabC55 0 4 3 1 1
  | _ => tabC55 0 4 3 1 2
def memRowC5510 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 0 4 3 1 3
  | 1 => tabC55 0 4 3 1 4
  | 2 => tabC55 0 4 3 2 0
  | 3 => tabC55 0 4 3 2 2
  | 4 => tabC55 0 4 3 2 3
  | 5 => tabC55 0 4 3 2 4
  | 6 => tabC55 0 4 3 3 0
  | 7 => tabC55 0 4 3 3 1
  | 8 => tabC55 0 4 3 3 2
  | 9 => tabC55 0 4 3 3 3
  | 10 => tabC55 0 4 3 3 4
  | 11 => tabC55 0 4 3 4 0
  | 12 => tabC55 0 4 3 4 1
  | 13 => tabC55 0 4 3 4 2
  | 14 => tabC55 0 4 3 4 3
  | 15 => tabC55 0 4 3 4 4
  | 16 => tabC55 0 4 4 0 0
  | 17 => tabC55 0 4 4 0 1
  | 18 => tabC55 0 4 4 0 2
  | 19 => tabC55 0 4 4 0 3
  | 20 => tabC55 0 4 4 0 4
  | 21 => tabC55 0 4 4 1 0
  | 22 => tabC55 0 4 4 1 1
  | 23 => tabC55 0 4 4 1 2
  | 24 => tabC55 0 4 4 1 3
  | 25 => tabC55 0 4 4 1 4
  | 26 => tabC55 0 4 4 2 0
  | 27 => tabC55 0 4 4 2 1
  | 28 => tabC55 0 4 4 2 3
  | 29 => tabC55 0 4 4 2 4
  | 30 => tabC55 0 4 4 3 0
  | 31 => tabC55 0 4 4 3 1
  | 32 => tabC55 0 4 4 3 2
  | 33 => tabC55 0 4 4 3 3
  | 34 => tabC55 0 4 4 3 4
  | 35 => tabC55 0 4 4 4 0
  | 36 => tabC55 0 4 4 4 1
  | 37 => tabC55 0 4 4 4 2
  | 38 => tabC55 0 4 4 4 3
  | 39 => tabC55 0 4 4 4 4
  | 40 => tabC55 1 0 0 0 0
  | 41 => tabC55 1 0 0 0 1
  | 42 => tabC55 1 0 0 0 2
  | 43 => tabC55 1 0 0 0 3
  | 44 => tabC55 1 0 0 0 4
  | 45 => tabC55 1 0 0 1 0
  | 46 => tabC55 1 0 0 1 1
  | 47 => tabC55 1 0 0 1 2
  | 48 => tabC55 1 0 0 1 3
  | 49 => tabC55 1 0 0 1 4
  | 50 => tabC55 1 0 0 2 0
  | 51 => tabC55 1 0 0 2 1
  | 52 => tabC55 1 0 0 2 2
  | 53 => tabC55 1 0 0 2 3
  | 54 => tabC55 1 0 0 2 4
  | _ => tabC55 1 0 0 3 0
def memRowC5511 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 0 0 3 1
  | 1 => tabC55 1 0 0 3 2
  | 2 => tabC55 1 0 0 3 3
  | 3 => tabC55 1 0 0 3 4
  | 4 => tabC55 1 0 0 4 0
  | 5 => tabC55 1 0 0 4 1
  | 6 => tabC55 1 0 0 4 2
  | 7 => tabC55 1 0 0 4 3
  | 8 => tabC55 1 0 0 4 4
  | 9 => tabC55 1 0 1 0 0
  | 10 => tabC55 1 0 1 0 1
  | 11 => tabC55 1 0 1 0 2
  | 12 => tabC55 1 0 1 0 3
  | 13 => tabC55 1 0 1 0 4
  | 14 => tabC55 1 0 1 1 0
  | 15 => tabC55 1 0 1 1 1
  | 16 => tabC55 1 0 1 1 2
  | 17 => tabC55 1 0 1 1 3
  | 18 => tabC55 1 0 1 1 4
  | 19 => tabC55 1 0 1 2 0
  | 20 => tabC55 1 0 1 2 1
  | 21 => tabC55 1 0 1 2 2
  | 22 => tabC55 1 0 1 2 3
  | 23 => tabC55 1 0 1 2 4
  | 24 => tabC55 1 0 1 3 0
  | 25 => tabC55 1 0 1 3 1
  | 26 => tabC55 1 0 1 3 2
  | 27 => tabC55 1 0 1 3 3
  | 28 => tabC55 1 0 1 3 4
  | 29 => tabC55 1 0 1 4 0
  | 30 => tabC55 1 0 1 4 1
  | 31 => tabC55 1 0 1 4 2
  | 32 => tabC55 1 0 1 4 3
  | 33 => tabC55 1 0 1 4 4
  | 34 => tabC55 1 0 2 0 0
  | 35 => tabC55 1 0 2 0 1
  | 36 => tabC55 1 0 2 0 2
  | 37 => tabC55 1 0 2 0 3
  | 38 => tabC55 1 0 2 0 4
  | 39 => tabC55 1 0 2 1 0
  | 40 => tabC55 1 0 2 1 1
  | 41 => tabC55 1 0 2 1 2
  | 42 => tabC55 1 0 2 1 3
  | 43 => tabC55 1 0 2 1 4
  | 44 => tabC55 1 0 2 2 0
  | 45 => tabC55 1 0 2 2 1
  | 46 => tabC55 1 0 2 2 2
  | 47 => tabC55 1 0 2 2 3
  | 48 => tabC55 1 0 2 2 4
  | 49 => tabC55 1 0 2 3 0
  | 50 => tabC55 1 0 2 3 1
  | 51 => tabC55 1 0 2 3 2
  | 52 => tabC55 1 0 2 3 3
  | 53 => tabC55 1 0 2 3 4
  | 54 => tabC55 1 0 2 4 0
  | _ => tabC55 1 0 2 4 1
def memRowC5512 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 0 2 4 2
  | 1 => tabC55 1 0 2 4 3
  | 2 => tabC55 1 0 2 4 4
  | 3 => tabC55 1 0 3 0 0
  | 4 => tabC55 1 0 3 0 1
  | 5 => tabC55 1 0 3 0 2
  | 6 => tabC55 1 0 3 0 3
  | 7 => tabC55 1 0 3 0 4
  | 8 => tabC55 1 0 3 1 0
  | 9 => tabC55 1 0 3 1 1
  | 10 => tabC55 1 0 3 1 2
  | 11 => tabC55 1 0 3 1 3
  | 12 => tabC55 1 0 3 1 4
  | 13 => tabC55 1 0 3 2 0
  | 14 => tabC55 1 0 3 2 1
  | 15 => tabC55 1 0 3 2 2
  | 16 => tabC55 1 0 3 2 3
  | 17 => tabC55 1 0 3 2 4
  | 18 => tabC55 1 0 3 3 0
  | 19 => tabC55 1 0 3 3 1
  | 20 => tabC55 1 0 3 3 2
  | 21 => tabC55 1 0 3 3 3
  | 22 => tabC55 1 0 3 3 4
  | 23 => tabC55 1 0 3 4 0
  | 24 => tabC55 1 0 3 4 1
  | 25 => tabC55 1 0 3 4 2
  | 26 => tabC55 1 0 3 4 3
  | 27 => tabC55 1 0 3 4 4
  | 28 => tabC55 1 0 4 0 0
  | 29 => tabC55 1 0 4 0 1
  | 30 => tabC55 1 0 4 0 2
  | 31 => tabC55 1 0 4 0 3
  | 32 => tabC55 1 0 4 0 4
  | 33 => tabC55 1 0 4 1 0
  | 34 => tabC55 1 0 4 1 1
  | 35 => tabC55 1 0 4 1 2
  | 36 => tabC55 1 0 4 1 3
  | 37 => tabC55 1 0 4 1 4
  | 38 => tabC55 1 0 4 2 0
  | 39 => tabC55 1 0 4 2 1
  | 40 => tabC55 1 0 4 2 2
  | 41 => tabC55 1 0 4 2 3
  | 42 => tabC55 1 0 4 2 4
  | 43 => tabC55 1 0 4 3 0
  | 44 => tabC55 1 0 4 3 1
  | 45 => tabC55 1 0 4 3 2
  | 46 => tabC55 1 0 4 3 3
  | 47 => tabC55 1 0 4 3 4
  | 48 => tabC55 1 0 4 4 0
  | 49 => tabC55 1 0 4 4 1
  | 50 => tabC55 1 0 4 4 2
  | 51 => tabC55 1 0 4 4 3
  | 52 => tabC55 1 0 4 4 4
  | 53 => tabC55 1 1 0 0 0
  | 54 => tabC55 1 1 0 0 1
  | _ => tabC55 1 1 0 0 2
def memRowC5513 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 1 0 0 3
  | 1 => tabC55 1 1 0 0 4
  | 2 => tabC55 1 1 0 1 0
  | 3 => tabC55 1 1 0 1 1
  | 4 => tabC55 1 1 0 1 2
  | 5 => tabC55 1 1 0 1 3
  | 6 => tabC55 1 1 0 1 4
  | 7 => tabC55 1 1 0 2 0
  | 8 => tabC55 1 1 0 2 1
  | 9 => tabC55 1 1 0 2 2
  | 10 => tabC55 1 1 0 2 3
  | 11 => tabC55 1 1 0 2 4
  | 12 => tabC55 1 1 0 3 0
  | 13 => tabC55 1 1 0 3 1
  | 14 => tabC55 1 1 0 3 2
  | 15 => tabC55 1 1 0 3 3
  | 16 => tabC55 1 1 0 3 4
  | 17 => tabC55 1 1 0 4 0
  | 18 => tabC55 1 1 0 4 1
  | 19 => tabC55 1 1 0 4 2
  | 20 => tabC55 1 1 0 4 3
  | 21 => tabC55 1 1 0 4 4
  | 22 => tabC55 1 1 1 0 0
  | 23 => tabC55 1 1 1 0 1
  | 24 => tabC55 1 1 1 0 2
  | 25 => tabC55 1 1 1 0 3
  | 26 => tabC55 1 1 1 0 4
  | 27 => tabC55 1 1 1 1 0
  | 28 => tabC55 1 1 1 1 1
  | 29 => tabC55 1 1 1 1 2
  | 30 => tabC55 1 1 1 1 3
  | 31 => tabC55 1 1 1 1 4
  | 32 => tabC55 1 1 1 2 0
  | 33 => tabC55 1 1 1 2 1
  | 34 => tabC55 1 1 1 2 2
  | 35 => tabC55 1 1 1 2 3
  | 36 => tabC55 1 1 1 2 4
  | 37 => tabC55 1 1 1 3 0
  | 38 => tabC55 1 1 1 3 1
  | 39 => tabC55 1 1 1 3 2
  | 40 => tabC55 1 1 1 3 3
  | 41 => tabC55 1 1 1 3 4
  | 42 => tabC55 1 1 1 4 0
  | 43 => tabC55 1 1 1 4 1
  | 44 => tabC55 1 1 1 4 2
  | 45 => tabC55 1 1 1 4 3
  | 46 => tabC55 1 1 1 4 4
  | 47 => tabC55 1 1 2 0 0
  | 48 => tabC55 1 1 2 0 1
  | 49 => tabC55 1 1 2 0 2
  | 50 => tabC55 1 1 2 0 3
  | 51 => tabC55 1 1 2 0 4
  | 52 => tabC55 1 1 2 1 0
  | 53 => tabC55 1 1 2 1 1
  | 54 => tabC55 1 1 2 1 2
  | _ => tabC55 1 1 2 1 3
def memRowC5514 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 1 2 1 4
  | 1 => tabC55 1 1 2 2 0
  | 2 => tabC55 1 1 2 2 1
  | 3 => tabC55 1 1 2 2 2
  | 4 => tabC55 1 1 2 2 3
  | 5 => tabC55 1 1 2 2 4
  | 6 => tabC55 1 1 2 3 0
  | 7 => tabC55 1 1 2 3 1
  | 8 => tabC55 1 1 2 3 2
  | 9 => tabC55 1 1 2 3 3
  | 10 => tabC55 1 1 2 3 4
  | 11 => tabC55 1 1 2 4 0
  | 12 => tabC55 1 1 2 4 1
  | 13 => tabC55 1 1 2 4 2
  | 14 => tabC55 1 1 2 4 3
  | 15 => tabC55 1 1 2 4 4
  | 16 => tabC55 1 1 3 0 0
  | 17 => tabC55 1 1 3 0 1
  | 18 => tabC55 1 1 3 0 2
  | 19 => tabC55 1 1 3 0 3
  | 20 => tabC55 1 1 3 0 4
  | 21 => tabC55 1 1 3 1 0
  | 22 => tabC55 1 1 3 1 1
  | 23 => tabC55 1 1 3 1 2
  | 24 => tabC55 1 1 3 1 3
  | 25 => tabC55 1 1 3 1 4
  | 26 => tabC55 1 1 3 2 0
  | 27 => tabC55 1 1 3 2 1
  | 28 => tabC55 1 1 3 2 2
  | 29 => tabC55 1 1 3 2 3
  | 30 => tabC55 1 1 3 2 4
  | 31 => tabC55 1 1 3 3 0
  | 32 => tabC55 1 1 3 3 1
  | 33 => tabC55 1 1 3 3 2
  | 34 => tabC55 1 1 3 3 3
  | 35 => tabC55 1 1 3 3 4
  | 36 => tabC55 1 1 3 4 0
  | 37 => tabC55 1 1 3 4 1
  | 38 => tabC55 1 1 3 4 2
  | 39 => tabC55 1 1 3 4 3
  | 40 => tabC55 1 1 3 4 4
  | 41 => tabC55 1 1 4 0 0
  | 42 => tabC55 1 1 4 0 1
  | 43 => tabC55 1 1 4 0 2
  | 44 => tabC55 1 1 4 0 3
  | 45 => tabC55 1 1 4 0 4
  | 46 => tabC55 1 1 4 1 0
  | 47 => tabC55 1 1 4 1 1
  | 48 => tabC55 1 1 4 1 2
  | 49 => tabC55 1 1 4 1 3
  | 50 => tabC55 1 1 4 1 4
  | 51 => tabC55 1 1 4 2 0
  | 52 => tabC55 1 1 4 2 1
  | 53 => tabC55 1 1 4 2 2
  | 54 => tabC55 1 1 4 2 3
  | _ => tabC55 1 1 4 2 4
def memRowC5515 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 1 4 3 0
  | 1 => tabC55 1 1 4 3 1
  | 2 => tabC55 1 1 4 3 2
  | 3 => tabC55 1 1 4 3 3
  | 4 => tabC55 1 1 4 3 4
  | 5 => tabC55 1 1 4 4 0
  | 6 => tabC55 1 1 4 4 1
  | 7 => tabC55 1 1 4 4 2
  | 8 => tabC55 1 1 4 4 3
  | 9 => tabC55 1 1 4 4 4
  | 10 => tabC55 1 2 0 0 0
  | 11 => tabC55 1 2 0 0 1
  | 12 => tabC55 1 2 0 0 2
  | 13 => tabC55 1 2 0 0 3
  | 14 => tabC55 1 2 0 0 4
  | 15 => tabC55 1 2 0 1 0
  | 16 => tabC55 1 2 0 1 1
  | 17 => tabC55 1 2 0 1 2
  | 18 => tabC55 1 2 0 1 3
  | 19 => tabC55 1 2 0 1 4
  | 20 => tabC55 1 2 0 2 0
  | 21 => tabC55 1 2 0 2 1
  | 22 => tabC55 1 2 0 2 2
  | 23 => tabC55 1 2 0 2 3
  | 24 => tabC55 1 2 0 2 4
  | 25 => tabC55 1 2 0 3 0
  | 26 => tabC55 1 2 0 3 1
  | 27 => tabC55 1 2 0 3 2
  | 28 => tabC55 1 2 0 3 3
  | 29 => tabC55 1 2 0 3 4
  | 30 => tabC55 1 2 0 4 0
  | 31 => tabC55 1 2 0 4 1
  | 32 => tabC55 1 2 0 4 2
  | 33 => tabC55 1 2 0 4 3
  | 34 => tabC55 1 2 0 4 4
  | 35 => tabC55 1 2 1 0 0
  | 36 => tabC55 1 2 1 0 1
  | 37 => tabC55 1 2 1 0 2
  | 38 => tabC55 1 2 1 0 3
  | 39 => tabC55 1 2 1 0 4
  | 40 => tabC55 1 2 1 1 0
  | 41 => tabC55 1 2 1 1 1
  | 42 => tabC55 1 2 1 1 2
  | 43 => tabC55 1 2 1 1 3
  | 44 => tabC55 1 2 1 1 4
  | 45 => tabC55 1 2 1 2 0
  | 46 => tabC55 1 2 1 2 1
  | 47 => tabC55 1 2 1 2 2
  | 48 => tabC55 1 2 1 2 3
  | 49 => tabC55 1 2 1 2 4
  | 50 => tabC55 1 2 1 3 0
  | 51 => tabC55 1 2 1 3 1
  | 52 => tabC55 1 2 1 3 2
  | 53 => tabC55 1 2 1 3 3
  | 54 => tabC55 1 2 1 3 4
  | _ => tabC55 1 2 1 4 0
def memRowC5516 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 2 1 4 1
  | 1 => tabC55 1 2 1 4 2
  | 2 => tabC55 1 2 1 4 3
  | 3 => tabC55 1 2 1 4 4
  | 4 => tabC55 1 2 2 0 0
  | 5 => tabC55 1 2 2 0 1
  | 6 => tabC55 1 2 2 0 2
  | 7 => tabC55 1 2 2 0 3
  | 8 => tabC55 1 2 2 0 4
  | 9 => tabC55 1 2 2 1 0
  | 10 => tabC55 1 2 2 1 1
  | 11 => tabC55 1 2 2 1 2
  | 12 => tabC55 1 2 2 1 3
  | 13 => tabC55 1 2 2 1 4
  | 14 => tabC55 1 2 2 2 0
  | 15 => tabC55 1 2 2 2 1
  | 16 => tabC55 1 2 2 2 2
  | 17 => tabC55 1 2 2 2 3
  | 18 => tabC55 1 2 2 2 4
  | 19 => tabC55 1 2 2 3 0
  | 20 => tabC55 1 2 2 3 1
  | 21 => tabC55 1 2 2 3 2
  | 22 => tabC55 1 2 2 3 3
  | 23 => tabC55 1 2 2 3 4
  | 24 => tabC55 1 2 2 4 0
  | 25 => tabC55 1 2 2 4 1
  | 26 => tabC55 1 2 2 4 2
  | 27 => tabC55 1 2 2 4 3
  | 28 => tabC55 1 2 2 4 4
  | 29 => tabC55 1 2 3 0 0
  | 30 => tabC55 1 2 3 0 1
  | 31 => tabC55 1 2 3 0 2
  | 32 => tabC55 1 2 3 0 3
  | 33 => tabC55 1 2 3 0 4
  | 34 => tabC55 1 2 3 1 0
  | 35 => tabC55 1 2 3 1 1
  | 36 => tabC55 1 2 3 1 2
  | 37 => tabC55 1 2 3 1 3
  | 38 => tabC55 1 2 3 1 4
  | 39 => tabC55 1 2 3 2 0
  | 40 => tabC55 1 2 3 2 1
  | 41 => tabC55 1 2 3 2 2
  | 42 => tabC55 1 2 3 2 3
  | 43 => tabC55 1 2 3 2 4
  | 44 => tabC55 1 2 3 3 0
  | 45 => tabC55 1 2 3 3 1
  | 46 => tabC55 1 2 3 3 2
  | 47 => tabC55 1 2 3 3 3
  | 48 => tabC55 1 2 3 3 4
  | 49 => tabC55 1 2 3 4 0
  | 50 => tabC55 1 2 3 4 1
  | 51 => tabC55 1 2 3 4 2
  | 52 => tabC55 1 2 3 4 3
  | 53 => tabC55 1 2 3 4 4
  | 54 => tabC55 1 2 4 0 0
  | _ => tabC55 1 2 4 0 1
def memRowC5517 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 2 4 0 2
  | 1 => tabC55 1 2 4 0 3
  | 2 => tabC55 1 2 4 0 4
  | 3 => tabC55 1 2 4 1 0
  | 4 => tabC55 1 2 4 1 1
  | 5 => tabC55 1 2 4 1 2
  | 6 => tabC55 1 2 4 1 3
  | 7 => tabC55 1 2 4 1 4
  | 8 => tabC55 1 2 4 2 0
  | 9 => tabC55 1 2 4 2 1
  | 10 => tabC55 1 2 4 2 2
  | 11 => tabC55 1 2 4 2 3
  | 12 => tabC55 1 2 4 2 4
  | 13 => tabC55 1 2 4 3 0
  | 14 => tabC55 1 2 4 3 1
  | 15 => tabC55 1 2 4 3 2
  | 16 => tabC55 1 2 4 3 3
  | 17 => tabC55 1 2 4 3 4
  | 18 => tabC55 1 2 4 4 0
  | 19 => tabC55 1 2 4 4 1
  | 20 => tabC55 1 2 4 4 2
  | 21 => tabC55 1 2 4 4 3
  | 22 => tabC55 1 2 4 4 4
  | 23 => tabC55 1 3 0 0 0
  | 24 => tabC55 1 3 0 0 1
  | 25 => tabC55 1 3 0 0 2
  | 26 => tabC55 1 3 0 0 3
  | 27 => tabC55 1 3 0 0 4
  | 28 => tabC55 1 3 0 1 0
  | 29 => tabC55 1 3 0 1 1
  | 30 => tabC55 1 3 0 1 2
  | 31 => tabC55 1 3 0 1 3
  | 32 => tabC55 1 3 0 1 4
  | 33 => tabC55 1 3 0 2 0
  | 34 => tabC55 1 3 0 2 1
  | 35 => tabC55 1 3 0 2 2
  | 36 => tabC55 1 3 0 2 3
  | 37 => tabC55 1 3 0 2 4
  | 38 => tabC55 1 3 0 3 0
  | 39 => tabC55 1 3 0 3 1
  | 40 => tabC55 1 3 0 3 2
  | 41 => tabC55 1 3 0 3 3
  | 42 => tabC55 1 3 0 3 4
  | 43 => tabC55 1 3 0 4 0
  | 44 => tabC55 1 3 0 4 1
  | 45 => tabC55 1 3 0 4 2
  | 46 => tabC55 1 3 0 4 3
  | 47 => tabC55 1 3 0 4 4
  | 48 => tabC55 1 3 1 0 0
  | 49 => tabC55 1 3 1 0 1
  | 50 => tabC55 1 3 1 0 2
  | 51 => tabC55 1 3 1 0 3
  | 52 => tabC55 1 3 1 0 4
  | 53 => tabC55 1 3 1 1 0
  | 54 => tabC55 1 3 1 1 1
  | _ => tabC55 1 3 1 1 2
def memRowC5518 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 3 1 1 3
  | 1 => tabC55 1 3 1 1 4
  | 2 => tabC55 1 3 1 2 0
  | 3 => tabC55 1 3 1 2 1
  | 4 => tabC55 1 3 1 2 2
  | 5 => tabC55 1 3 1 2 3
  | 6 => tabC55 1 3 1 2 4
  | 7 => tabC55 1 3 1 3 0
  | 8 => tabC55 1 3 1 3 1
  | 9 => tabC55 1 3 1 3 2
  | 10 => tabC55 1 3 1 3 3
  | 11 => tabC55 1 3 1 3 4
  | 12 => tabC55 1 3 1 4 0
  | 13 => tabC55 1 3 1 4 1
  | 14 => tabC55 1 3 1 4 2
  | 15 => tabC55 1 3 1 4 3
  | 16 => tabC55 1 3 1 4 4
  | 17 => tabC55 1 3 2 0 0
  | 18 => tabC55 1 3 2 0 1
  | 19 => tabC55 1 3 2 0 2
  | 20 => tabC55 1 3 2 0 3
  | 21 => tabC55 1 3 2 0 4
  | 22 => tabC55 1 3 2 1 0
  | 23 => tabC55 1 3 2 1 1
  | 24 => tabC55 1 3 2 1 2
  | 25 => tabC55 1 3 2 1 3
  | 26 => tabC55 1 3 2 1 4
  | 27 => tabC55 1 3 2 2 0
  | 28 => tabC55 1 3 2 2 1
  | 29 => tabC55 1 3 2 2 2
  | 30 => tabC55 1 3 2 2 3
  | 31 => tabC55 1 3 2 2 4
  | 32 => tabC55 1 3 2 3 0
  | 33 => tabC55 1 3 2 3 1
  | 34 => tabC55 1 3 2 3 2
  | 35 => tabC55 1 3 2 3 3
  | 36 => tabC55 1 3 2 3 4
  | 37 => tabC55 1 3 2 4 0
  | 38 => tabC55 1 3 2 4 1
  | 39 => tabC55 1 3 2 4 2
  | 40 => tabC55 1 3 2 4 3
  | 41 => tabC55 1 3 2 4 4
  | 42 => tabC55 1 3 3 0 0
  | 43 => tabC55 1 3 3 0 1
  | 44 => tabC55 1 3 3 0 2
  | 45 => tabC55 1 3 3 0 3
  | 46 => tabC55 1 3 3 0 4
  | 47 => tabC55 1 3 3 1 0
  | 48 => tabC55 1 3 3 1 1
  | 49 => tabC55 1 3 3 1 2
  | 50 => tabC55 1 3 3 1 3
  | 51 => tabC55 1 3 3 1 4
  | 52 => tabC55 1 3 3 2 0
  | 53 => tabC55 1 3 3 2 1
  | 54 => tabC55 1 3 3 2 2
  | _ => tabC55 1 3 3 2 3
def memRowC5519 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 3 3 2 4
  | 1 => tabC55 1 3 3 3 0
  | 2 => tabC55 1 3 3 3 1
  | 3 => tabC55 1 3 3 3 2
  | 4 => tabC55 1 3 3 3 3
  | 5 => tabC55 1 3 3 3 4
  | 6 => tabC55 1 3 3 4 0
  | 7 => tabC55 1 3 3 4 1
  | 8 => tabC55 1 3 3 4 2
  | 9 => tabC55 1 3 3 4 3
  | 10 => tabC55 1 3 3 4 4
  | 11 => tabC55 1 3 4 0 0
  | 12 => tabC55 1 3 4 0 1
  | 13 => tabC55 1 3 4 0 2
  | 14 => tabC55 1 3 4 0 3
  | 15 => tabC55 1 3 4 0 4
  | 16 => tabC55 1 3 4 1 0
  | 17 => tabC55 1 3 4 1 1
  | 18 => tabC55 1 3 4 1 2
  | 19 => tabC55 1 3 4 1 3
  | 20 => tabC55 1 3 4 1 4
  | 21 => tabC55 1 3 4 2 0
  | 22 => tabC55 1 3 4 2 1
  | 23 => tabC55 1 3 4 2 2
  | 24 => tabC55 1 3 4 2 3
  | 25 => tabC55 1 3 4 2 4
  | 26 => tabC55 1 3 4 3 0
  | 27 => tabC55 1 3 4 3 1
  | 28 => tabC55 1 3 4 3 2
  | 29 => tabC55 1 3 4 3 3
  | 30 => tabC55 1 3 4 3 4
  | 31 => tabC55 1 3 4 4 0
  | 32 => tabC55 1 3 4 4 1
  | 33 => tabC55 1 3 4 4 2
  | 34 => tabC55 1 3 4 4 3
  | 35 => tabC55 1 3 4 4 4
  | 36 => tabC55 1 4 0 0 0
  | 37 => tabC55 1 4 0 0 1
  | 38 => tabC55 1 4 0 0 2
  | 39 => tabC55 1 4 0 0 3
  | 40 => tabC55 1 4 0 0 4
  | 41 => tabC55 1 4 0 1 0
  | 42 => tabC55 1 4 0 1 1
  | 43 => tabC55 1 4 0 1 2
  | 44 => tabC55 1 4 0 1 3
  | 45 => tabC55 1 4 0 1 4
  | 46 => tabC55 1 4 0 2 0
  | 47 => tabC55 1 4 0 2 1
  | 48 => tabC55 1 4 0 2 2
  | 49 => tabC55 1 4 0 2 3
  | 50 => tabC55 1 4 0 2 4
  | 51 => tabC55 1 4 0 3 0
  | 52 => tabC55 1 4 0 3 1
  | 53 => tabC55 1 4 0 3 2
  | 54 => tabC55 1 4 0 3 3
  | _ => tabC55 1 4 0 3 4
def memRowC5520 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 4 0 4 0
  | 1 => tabC55 1 4 0 4 1
  | 2 => tabC55 1 4 0 4 2
  | 3 => tabC55 1 4 0 4 3
  | 4 => tabC55 1 4 0 4 4
  | 5 => tabC55 1 4 1 0 0
  | 6 => tabC55 1 4 1 0 1
  | 7 => tabC55 1 4 1 0 2
  | 8 => tabC55 1 4 1 0 3
  | 9 => tabC55 1 4 1 0 4
  | 10 => tabC55 1 4 1 1 0
  | 11 => tabC55 1 4 1 1 1
  | 12 => tabC55 1 4 1 1 2
  | 13 => tabC55 1 4 1 1 3
  | 14 => tabC55 1 4 1 1 4
  | 15 => tabC55 1 4 1 2 0
  | 16 => tabC55 1 4 1 2 1
  | 17 => tabC55 1 4 1 2 2
  | 18 => tabC55 1 4 1 2 3
  | 19 => tabC55 1 4 1 2 4
  | 20 => tabC55 1 4 1 3 0
  | 21 => tabC55 1 4 1 3 1
  | 22 => tabC55 1 4 1 3 2
  | 23 => tabC55 1 4 1 3 3
  | 24 => tabC55 1 4 1 3 4
  | 25 => tabC55 1 4 1 4 0
  | 26 => tabC55 1 4 1 4 1
  | 27 => tabC55 1 4 1 4 2
  | 28 => tabC55 1 4 1 4 3
  | 29 => tabC55 1 4 1 4 4
  | 30 => tabC55 1 4 2 0 0
  | 31 => tabC55 1 4 2 0 1
  | 32 => tabC55 1 4 2 0 2
  | 33 => tabC55 1 4 2 0 3
  | 34 => tabC55 1 4 2 0 4
  | 35 => tabC55 1 4 2 1 0
  | 36 => tabC55 1 4 2 1 1
  | 37 => tabC55 1 4 2 1 2
  | 38 => tabC55 1 4 2 1 3
  | 39 => tabC55 1 4 2 1 4
  | 40 => tabC55 1 4 2 2 0
  | 41 => tabC55 1 4 2 2 1
  | 42 => tabC55 1 4 2 2 2
  | 43 => tabC55 1 4 2 2 3
  | 44 => tabC55 1 4 2 2 4
  | 45 => tabC55 1 4 2 3 0
  | 46 => tabC55 1 4 2 3 1
  | 47 => tabC55 1 4 2 3 2
  | 48 => tabC55 1 4 2 3 3
  | 49 => tabC55 1 4 2 3 4
  | 50 => tabC55 1 4 2 4 0
  | 51 => tabC55 1 4 2 4 1
  | 52 => tabC55 1 4 2 4 2
  | 53 => tabC55 1 4 2 4 3
  | 54 => tabC55 1 4 2 4 4
  | _ => tabC55 1 4 3 0 0
def memRowC5521 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 1 4 3 0 1
  | 1 => tabC55 1 4 3 0 2
  | 2 => tabC55 1 4 3 0 3
  | 3 => tabC55 1 4 3 0 4
  | 4 => tabC55 1 4 3 1 0
  | 5 => tabC55 1 4 3 1 1
  | 6 => tabC55 1 4 3 1 2
  | 7 => tabC55 1 4 3 1 3
  | 8 => tabC55 1 4 3 1 4
  | 9 => tabC55 1 4 3 2 0
  | 10 => tabC55 1 4 3 2 1
  | 11 => tabC55 1 4 3 2 2
  | 12 => tabC55 1 4 3 2 3
  | 13 => tabC55 1 4 3 2 4
  | 14 => tabC55 1 4 3 3 0
  | 15 => tabC55 1 4 3 3 1
  | 16 => tabC55 1 4 3 3 2
  | 17 => tabC55 1 4 3 3 3
  | 18 => tabC55 1 4 3 3 4
  | 19 => tabC55 1 4 3 4 0
  | 20 => tabC55 1 4 3 4 1
  | 21 => tabC55 1 4 3 4 2
  | 22 => tabC55 1 4 3 4 3
  | 23 => tabC55 1 4 3 4 4
  | 24 => tabC55 1 4 4 0 0
  | 25 => tabC55 1 4 4 0 1
  | 26 => tabC55 1 4 4 0 2
  | 27 => tabC55 1 4 4 0 3
  | 28 => tabC55 1 4 4 0 4
  | 29 => tabC55 1 4 4 1 0
  | 30 => tabC55 1 4 4 1 1
  | 31 => tabC55 1 4 4 1 2
  | 32 => tabC55 1 4 4 1 3
  | 33 => tabC55 1 4 4 1 4
  | 34 => tabC55 1 4 4 2 0
  | 35 => tabC55 1 4 4 2 1
  | 36 => tabC55 1 4 4 2 2
  | 37 => tabC55 1 4 4 2 3
  | 38 => tabC55 1 4 4 2 4
  | 39 => tabC55 1 4 4 3 0
  | 40 => tabC55 1 4 4 3 1
  | 41 => tabC55 1 4 4 3 2
  | 42 => tabC55 1 4 4 3 3
  | 43 => tabC55 1 4 4 3 4
  | 44 => tabC55 1 4 4 4 0
  | 45 => tabC55 1 4 4 4 1
  | 46 => tabC55 1 4 4 4 2
  | 47 => tabC55 1 4 4 4 3
  | 48 => tabC55 1 4 4 4 4
  | 49 => tabC55 2 0 0 0 0
  | 50 => tabC55 2 0 0 0 1
  | 51 => tabC55 2 0 0 0 2
  | 52 => tabC55 2 0 0 0 3
  | 53 => tabC55 2 0 0 0 4
  | 54 => tabC55 2 0 0 1 0
  | _ => tabC55 2 0 0 1 1
def memRowC5522 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 0 0 1 2
  | 1 => tabC55 2 0 0 1 3
  | 2 => tabC55 2 0 0 1 4
  | 3 => tabC55 2 0 0 2 0
  | 4 => tabC55 2 0 0 2 1
  | 5 => tabC55 2 0 0 2 2
  | 6 => tabC55 2 0 0 2 3
  | 7 => tabC55 2 0 0 2 4
  | 8 => tabC55 2 0 0 3 0
  | 9 => tabC55 2 0 0 3 1
  | 10 => tabC55 2 0 0 3 2
  | 11 => tabC55 2 0 0 3 3
  | 12 => tabC55 2 0 0 3 4
  | 13 => tabC55 2 0 0 4 0
  | 14 => tabC55 2 0 0 4 1
  | 15 => tabC55 2 0 0 4 2
  | 16 => tabC55 2 0 0 4 3
  | 17 => tabC55 2 0 0 4 4
  | 18 => tabC55 2 0 1 0 0
  | 19 => tabC55 2 0 1 0 1
  | 20 => tabC55 2 0 1 0 2
  | 21 => tabC55 2 0 1 0 3
  | 22 => tabC55 2 0 1 0 4
  | 23 => tabC55 2 0 1 1 0
  | 24 => tabC55 2 0 1 1 1
  | 25 => tabC55 2 0 1 1 2
  | 26 => tabC55 2 0 1 1 3
  | 27 => tabC55 2 0 1 1 4
  | 28 => tabC55 2 0 1 2 0
  | 29 => tabC55 2 0 1 2 1
  | 30 => tabC55 2 0 1 2 2
  | 31 => tabC55 2 0 1 2 3
  | 32 => tabC55 2 0 1 2 4
  | 33 => tabC55 2 0 1 3 0
  | 34 => tabC55 2 0 1 3 1
  | 35 => tabC55 2 0 1 3 2
  | 36 => tabC55 2 0 1 3 3
  | 37 => tabC55 2 0 1 3 4
  | 38 => tabC55 2 0 1 4 0
  | 39 => tabC55 2 0 1 4 1
  | 40 => tabC55 2 0 1 4 2
  | 41 => tabC55 2 0 1 4 3
  | 42 => tabC55 2 0 1 4 4
  | 43 => tabC55 2 0 2 0 0
  | 44 => tabC55 2 0 2 0 1
  | 45 => tabC55 2 0 2 0 2
  | 46 => tabC55 2 0 2 0 3
  | 47 => tabC55 2 0 2 0 4
  | 48 => tabC55 2 0 2 1 0
  | 49 => tabC55 2 0 2 1 1
  | 50 => tabC55 2 0 2 1 2
  | 51 => tabC55 2 0 2 1 3
  | 52 => tabC55 2 0 2 1 4
  | 53 => tabC55 2 0 2 2 0
  | 54 => tabC55 2 0 2 2 1
  | _ => tabC55 2 0 2 2 2
def memRowC5523 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 0 2 2 3
  | 1 => tabC55 2 0 2 2 4
  | 2 => tabC55 2 0 2 3 0
  | 3 => tabC55 2 0 2 3 1
  | 4 => tabC55 2 0 2 3 2
  | 5 => tabC55 2 0 2 3 3
  | 6 => tabC55 2 0 2 3 4
  | 7 => tabC55 2 0 2 4 0
  | 8 => tabC55 2 0 2 4 1
  | 9 => tabC55 2 0 2 4 2
  | 10 => tabC55 2 0 2 4 3
  | 11 => tabC55 2 0 2 4 4
  | 12 => tabC55 2 0 3 0 0
  | 13 => tabC55 2 0 3 0 1
  | 14 => tabC55 2 0 3 0 2
  | 15 => tabC55 2 0 3 0 3
  | 16 => tabC55 2 0 3 0 4
  | 17 => tabC55 2 0 3 1 0
  | 18 => tabC55 2 0 3 1 1
  | 19 => tabC55 2 0 3 1 2
  | 20 => tabC55 2 0 3 1 3
  | 21 => tabC55 2 0 3 1 4
  | 22 => tabC55 2 0 3 2 0
  | 23 => tabC55 2 0 3 2 1
  | 24 => tabC55 2 0 3 2 2
  | 25 => tabC55 2 0 3 2 3
  | 26 => tabC55 2 0 3 2 4
  | 27 => tabC55 2 0 3 3 0
  | 28 => tabC55 2 0 3 3 1
  | 29 => tabC55 2 0 3 3 2
  | 30 => tabC55 2 0 3 3 3
  | 31 => tabC55 2 0 3 3 4
  | 32 => tabC55 2 0 3 4 0
  | 33 => tabC55 2 0 3 4 1
  | 34 => tabC55 2 0 3 4 2
  | 35 => tabC55 2 0 3 4 3
  | 36 => tabC55 2 0 3 4 4
  | 37 => tabC55 2 0 4 0 0
  | 38 => tabC55 2 0 4 0 1
  | 39 => tabC55 2 0 4 0 2
  | 40 => tabC55 2 0 4 0 3
  | 41 => tabC55 2 0 4 0 4
  | 42 => tabC55 2 0 4 1 0
  | 43 => tabC55 2 0 4 1 1
  | 44 => tabC55 2 0 4 1 2
  | 45 => tabC55 2 0 4 1 3
  | 46 => tabC55 2 0 4 1 4
  | 47 => tabC55 2 0 4 2 0
  | 48 => tabC55 2 0 4 2 1
  | 49 => tabC55 2 0 4 2 2
  | 50 => tabC55 2 0 4 2 3
  | 51 => tabC55 2 0 4 2 4
  | 52 => tabC55 2 0 4 3 0
  | 53 => tabC55 2 0 4 3 1
  | 54 => tabC55 2 0 4 3 2
  | _ => tabC55 2 0 4 3 3
def memRowC5524 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 0 4 3 4
  | 1 => tabC55 2 0 4 4 0
  | 2 => tabC55 2 0 4 4 1
  | 3 => tabC55 2 0 4 4 2
  | 4 => tabC55 2 0 4 4 3
  | 5 => tabC55 2 0 4 4 4
  | 6 => tabC55 2 1 0 0 0
  | 7 => tabC55 2 1 0 0 1
  | 8 => tabC55 2 1 0 0 2
  | 9 => tabC55 2 1 0 0 3
  | 10 => tabC55 2 1 0 0 4
  | 11 => tabC55 2 1 0 1 0
  | 12 => tabC55 2 1 0 1 1
  | 13 => tabC55 2 1 0 1 2
  | 14 => tabC55 2 1 0 1 3
  | 15 => tabC55 2 1 0 1 4
  | 16 => tabC55 2 1 0 2 0
  | 17 => tabC55 2 1 0 2 1
  | 18 => tabC55 2 1 0 2 2
  | 19 => tabC55 2 1 0 2 3
  | 20 => tabC55 2 1 0 2 4
  | 21 => tabC55 2 1 0 3 0
  | 22 => tabC55 2 1 0 3 1
  | 23 => tabC55 2 1 0 3 2
  | 24 => tabC55 2 1 0 3 3
  | 25 => tabC55 2 1 0 3 4
  | 26 => tabC55 2 1 0 4 0
  | 27 => tabC55 2 1 0 4 1
  | 28 => tabC55 2 1 0 4 2
  | 29 => tabC55 2 1 0 4 3
  | 30 => tabC55 2 1 0 4 4
  | 31 => tabC55 2 1 1 0 0
  | 32 => tabC55 2 1 1 0 1
  | 33 => tabC55 2 1 1 0 2
  | 34 => tabC55 2 1 1 0 3
  | 35 => tabC55 2 1 1 0 4
  | 36 => tabC55 2 1 1 1 0
  | 37 => tabC55 2 1 1 1 1
  | 38 => tabC55 2 1 1 1 2
  | 39 => tabC55 2 1 1 1 3
  | 40 => tabC55 2 1 1 1 4
  | 41 => tabC55 2 1 1 2 0
  | 42 => tabC55 2 1 1 2 1
  | 43 => tabC55 2 1 1 2 2
  | 44 => tabC55 2 1 1 2 3
  | 45 => tabC55 2 1 1 2 4
  | 46 => tabC55 2 1 1 3 0
  | 47 => tabC55 2 1 1 3 1
  | 48 => tabC55 2 1 1 3 2
  | 49 => tabC55 2 1 1 3 3
  | 50 => tabC55 2 1 1 3 4
  | 51 => tabC55 2 1 1 4 0
  | 52 => tabC55 2 1 1 4 1
  | 53 => tabC55 2 1 1 4 2
  | 54 => tabC55 2 1 1 4 3
  | _ => tabC55 2 1 1 4 4
def memRowC5525 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 1 2 0 0
  | 1 => tabC55 2 1 2 0 1
  | 2 => tabC55 2 1 2 0 2
  | 3 => tabC55 2 1 2 0 3
  | 4 => tabC55 2 1 2 0 4
  | 5 => tabC55 2 1 2 1 0
  | 6 => tabC55 2 1 2 1 1
  | 7 => tabC55 2 1 2 1 2
  | 8 => tabC55 2 1 2 1 3
  | 9 => tabC55 2 1 2 1 4
  | 10 => tabC55 2 1 2 2 0
  | 11 => tabC55 2 1 2 2 1
  | 12 => tabC55 2 1 2 2 2
  | 13 => tabC55 2 1 2 2 3
  | 14 => tabC55 2 1 2 2 4
  | 15 => tabC55 2 1 2 3 0
  | 16 => tabC55 2 1 2 3 1
  | 17 => tabC55 2 1 2 3 2
  | 18 => tabC55 2 1 2 3 3
  | 19 => tabC55 2 1 2 3 4
  | 20 => tabC55 2 1 2 4 0
  | 21 => tabC55 2 1 2 4 1
  | 22 => tabC55 2 1 2 4 2
  | 23 => tabC55 2 1 2 4 3
  | 24 => tabC55 2 1 2 4 4
  | 25 => tabC55 2 1 3 0 0
  | 26 => tabC55 2 1 3 0 1
  | 27 => tabC55 2 1 3 0 2
  | 28 => tabC55 2 1 3 0 3
  | 29 => tabC55 2 1 3 0 4
  | 30 => tabC55 2 1 3 1 0
  | 31 => tabC55 2 1 3 1 1
  | 32 => tabC55 2 1 3 1 2
  | 33 => tabC55 2 1 3 1 3
  | 34 => tabC55 2 1 3 1 4
  | 35 => tabC55 2 1 3 2 0
  | 36 => tabC55 2 1 3 2 1
  | 37 => tabC55 2 1 3 2 2
  | 38 => tabC55 2 1 3 2 3
  | 39 => tabC55 2 1 3 2 4
  | 40 => tabC55 2 1 3 3 0
  | 41 => tabC55 2 1 3 3 1
  | 42 => tabC55 2 1 3 3 2
  | 43 => tabC55 2 1 3 3 3
  | 44 => tabC55 2 1 3 3 4
  | 45 => tabC55 2 1 3 4 0
  | 46 => tabC55 2 1 3 4 1
  | 47 => tabC55 2 1 3 4 2
  | 48 => tabC55 2 1 3 4 3
  | 49 => tabC55 2 1 3 4 4
  | 50 => tabC55 2 1 4 0 0
  | 51 => tabC55 2 1 4 0 1
  | 52 => tabC55 2 1 4 0 2
  | 53 => tabC55 2 1 4 0 3
  | 54 => tabC55 2 1 4 0 4
  | _ => tabC55 2 1 4 1 0
def memRowC5526 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 1 4 1 1
  | 1 => tabC55 2 1 4 1 2
  | 2 => tabC55 2 1 4 1 3
  | 3 => tabC55 2 1 4 1 4
  | 4 => tabC55 2 1 4 2 0
  | 5 => tabC55 2 1 4 2 1
  | 6 => tabC55 2 1 4 2 2
  | 7 => tabC55 2 1 4 2 3
  | 8 => tabC55 2 1 4 2 4
  | 9 => tabC55 2 1 4 3 0
  | 10 => tabC55 2 1 4 3 1
  | 11 => tabC55 2 1 4 3 2
  | 12 => tabC55 2 1 4 3 3
  | 13 => tabC55 2 1 4 3 4
  | 14 => tabC55 2 1 4 4 0
  | 15 => tabC55 2 1 4 4 1
  | 16 => tabC55 2 1 4 4 2
  | 17 => tabC55 2 1 4 4 3
  | 18 => tabC55 2 1 4 4 4
  | 19 => tabC55 2 2 0 0 0
  | 20 => tabC55 2 2 0 0 1
  | 21 => tabC55 2 2 0 0 2
  | 22 => tabC55 2 2 0 0 3
  | 23 => tabC55 2 2 0 0 4
  | 24 => tabC55 2 2 0 1 0
  | 25 => tabC55 2 2 0 1 1
  | 26 => tabC55 2 2 0 1 2
  | 27 => tabC55 2 2 0 1 3
  | 28 => tabC55 2 2 0 1 4
  | 29 => tabC55 2 2 0 2 0
  | 30 => tabC55 2 2 0 2 1
  | 31 => tabC55 2 2 0 2 2
  | 32 => tabC55 2 2 0 2 3
  | 33 => tabC55 2 2 0 2 4
  | 34 => tabC55 2 2 0 3 0
  | 35 => tabC55 2 2 0 3 1
  | 36 => tabC55 2 2 0 3 2
  | 37 => tabC55 2 2 0 3 3
  | 38 => tabC55 2 2 0 3 4
  | 39 => tabC55 2 2 0 4 0
  | 40 => tabC55 2 2 0 4 1
  | 41 => tabC55 2 2 0 4 2
  | 42 => tabC55 2 2 0 4 3
  | 43 => tabC55 2 2 0 4 4
  | 44 => tabC55 2 2 1 0 0
  | 45 => tabC55 2 2 1 0 1
  | 46 => tabC55 2 2 1 0 2
  | 47 => tabC55 2 2 1 0 3
  | 48 => tabC55 2 2 1 0 4
  | 49 => tabC55 2 2 1 1 0
  | 50 => tabC55 2 2 1 1 1
  | 51 => tabC55 2 2 1 1 2
  | 52 => tabC55 2 2 1 1 3
  | 53 => tabC55 2 2 1 1 4
  | 54 => tabC55 2 2 1 2 0
  | _ => tabC55 2 2 1 2 1
def memRowC5527 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 2 1 2 2
  | 1 => tabC55 2 2 1 2 3
  | 2 => tabC55 2 2 1 2 4
  | 3 => tabC55 2 2 1 3 0
  | 4 => tabC55 2 2 1 3 1
  | 5 => tabC55 2 2 1 3 2
  | 6 => tabC55 2 2 1 3 3
  | 7 => tabC55 2 2 1 3 4
  | 8 => tabC55 2 2 1 4 0
  | 9 => tabC55 2 2 1 4 1
  | 10 => tabC55 2 2 1 4 2
  | 11 => tabC55 2 2 1 4 3
  | 12 => tabC55 2 2 1 4 4
  | 13 => tabC55 2 2 2 0 0
  | 14 => tabC55 2 2 2 0 1
  | 15 => tabC55 2 2 2 0 2
  | 16 => tabC55 2 2 2 0 3
  | 17 => tabC55 2 2 2 0 4
  | 18 => tabC55 2 2 2 1 0
  | 19 => tabC55 2 2 2 1 1
  | 20 => tabC55 2 2 2 1 2
  | 21 => tabC55 2 2 2 1 3
  | 22 => tabC55 2 2 2 1 4
  | 23 => tabC55 2 2 2 2 0
  | 24 => tabC55 2 2 2 2 1
  | 25 => tabC55 2 2 2 2 2
  | 26 => tabC55 2 2 2 2 3
  | 27 => tabC55 2 2 2 2 4
  | 28 => tabC55 2 2 2 3 0
  | 29 => tabC55 2 2 2 3 1
  | 30 => tabC55 2 2 2 3 2
  | 31 => tabC55 2 2 2 3 3
  | 32 => tabC55 2 2 2 3 4
  | 33 => tabC55 2 2 2 4 0
  | 34 => tabC55 2 2 2 4 1
  | 35 => tabC55 2 2 2 4 2
  | 36 => tabC55 2 2 2 4 3
  | 37 => tabC55 2 2 2 4 4
  | 38 => tabC55 2 2 3 0 0
  | 39 => tabC55 2 2 3 0 1
  | 40 => tabC55 2 2 3 0 2
  | 41 => tabC55 2 2 3 0 3
  | 42 => tabC55 2 2 3 0 4
  | 43 => tabC55 2 2 3 1 0
  | 44 => tabC55 2 2 3 1 1
  | 45 => tabC55 2 2 3 1 2
  | 46 => tabC55 2 2 3 1 3
  | 47 => tabC55 2 2 3 1 4
  | 48 => tabC55 2 2 3 2 0
  | 49 => tabC55 2 2 3 2 1
  | 50 => tabC55 2 2 3 2 2
  | 51 => tabC55 2 2 3 2 3
  | 52 => tabC55 2 2 3 2 4
  | 53 => tabC55 2 2 3 3 0
  | 54 => tabC55 2 2 3 3 1
  | _ => tabC55 2 2 3 3 2
def memRowC5528 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 2 3 3 3
  | 1 => tabC55 2 2 3 3 4
  | 2 => tabC55 2 2 3 4 0
  | 3 => tabC55 2 2 3 4 1
  | 4 => tabC55 2 2 3 4 2
  | 5 => tabC55 2 2 3 4 3
  | 6 => tabC55 2 2 3 4 4
  | 7 => tabC55 2 2 4 0 0
  | 8 => tabC55 2 2 4 0 1
  | 9 => tabC55 2 2 4 0 2
  | 10 => tabC55 2 2 4 0 3
  | 11 => tabC55 2 2 4 0 4
  | 12 => tabC55 2 2 4 1 0
  | 13 => tabC55 2 2 4 1 1
  | 14 => tabC55 2 2 4 1 2
  | 15 => tabC55 2 2 4 1 3
  | 16 => tabC55 2 2 4 1 4
  | 17 => tabC55 2 2 4 2 0
  | 18 => tabC55 2 2 4 2 1
  | 19 => tabC55 2 2 4 2 2
  | 20 => tabC55 2 2 4 2 3
  | 21 => tabC55 2 2 4 2 4
  | 22 => tabC55 2 2 4 3 0
  | 23 => tabC55 2 2 4 3 1
  | 24 => tabC55 2 2 4 3 2
  | 25 => tabC55 2 2 4 3 3
  | 26 => tabC55 2 2 4 3 4
  | 27 => tabC55 2 2 4 4 0
  | 28 => tabC55 2 2 4 4 1
  | 29 => tabC55 2 2 4 4 2
  | 30 => tabC55 2 2 4 4 3
  | 31 => tabC55 2 2 4 4 4
  | 32 => tabC55 2 3 0 0 0
  | 33 => tabC55 2 3 0 0 1
  | 34 => tabC55 2 3 0 0 2
  | 35 => tabC55 2 3 0 0 3
  | 36 => tabC55 2 3 0 0 4
  | 37 => tabC55 2 3 0 1 0
  | 38 => tabC55 2 3 0 1 1
  | 39 => tabC55 2 3 0 1 2
  | 40 => tabC55 2 3 0 1 3
  | 41 => tabC55 2 3 0 1 4
  | 42 => tabC55 2 3 0 2 0
  | 43 => tabC55 2 3 0 2 1
  | 44 => tabC55 2 3 0 2 2
  | 45 => tabC55 2 3 0 2 3
  | 46 => tabC55 2 3 0 2 4
  | 47 => tabC55 2 3 0 3 0
  | 48 => tabC55 2 3 0 3 1
  | 49 => tabC55 2 3 0 3 2
  | 50 => tabC55 2 3 0 3 3
  | 51 => tabC55 2 3 0 3 4
  | 52 => tabC55 2 3 0 4 0
  | 53 => tabC55 2 3 0 4 1
  | 54 => tabC55 2 3 0 4 2
  | _ => tabC55 2 3 0 4 3
def memRowC5529 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 3 0 4 4
  | 1 => tabC55 2 3 1 0 0
  | 2 => tabC55 2 3 1 0 1
  | 3 => tabC55 2 3 1 0 2
  | 4 => tabC55 2 3 1 0 3
  | 5 => tabC55 2 3 1 0 4
  | 6 => tabC55 2 3 1 1 0
  | 7 => tabC55 2 3 1 1 1
  | 8 => tabC55 2 3 1 1 2
  | 9 => tabC55 2 3 1 1 3
  | 10 => tabC55 2 3 1 1 4
  | 11 => tabC55 2 3 1 2 0
  | 12 => tabC55 2 3 1 2 1
  | 13 => tabC55 2 3 1 2 2
  | 14 => tabC55 2 3 1 2 3
  | 15 => tabC55 2 3 1 2 4
  | 16 => tabC55 2 3 1 3 0
  | 17 => tabC55 2 3 1 3 1
  | 18 => tabC55 2 3 1 3 2
  | 19 => tabC55 2 3 1 3 3
  | 20 => tabC55 2 3 1 3 4
  | 21 => tabC55 2 3 1 4 0
  | 22 => tabC55 2 3 1 4 1
  | 23 => tabC55 2 3 1 4 2
  | 24 => tabC55 2 3 1 4 3
  | 25 => tabC55 2 3 1 4 4
  | 26 => tabC55 2 3 2 0 0
  | 27 => tabC55 2 3 2 0 1
  | 28 => tabC55 2 3 2 0 2
  | 29 => tabC55 2 3 2 0 3
  | 30 => tabC55 2 3 2 0 4
  | 31 => tabC55 2 3 2 1 0
  | 32 => tabC55 2 3 2 1 1
  | 33 => tabC55 2 3 2 1 2
  | 34 => tabC55 2 3 2 1 3
  | 35 => tabC55 2 3 2 1 4
  | 36 => tabC55 2 3 2 2 0
  | 37 => tabC55 2 3 2 2 1
  | 38 => tabC55 2 3 2 2 2
  | 39 => tabC55 2 3 2 2 3
  | 40 => tabC55 2 3 2 2 4
  | 41 => tabC55 2 3 2 3 0
  | 42 => tabC55 2 3 2 3 1
  | 43 => tabC55 2 3 2 3 2
  | 44 => tabC55 2 3 2 3 3
  | 45 => tabC55 2 3 2 3 4
  | 46 => tabC55 2 3 2 4 0
  | 47 => tabC55 2 3 2 4 1
  | 48 => tabC55 2 3 2 4 2
  | 49 => tabC55 2 3 2 4 3
  | 50 => tabC55 2 3 2 4 4
  | 51 => tabC55 2 3 3 0 0
  | 52 => tabC55 2 3 3 0 1
  | 53 => tabC55 2 3 3 0 2
  | 54 => tabC55 2 3 3 0 3
  | _ => tabC55 2 3 3 0 4
def memRowC5530 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 3 3 1 0
  | 1 => tabC55 2 3 3 1 1
  | 2 => tabC55 2 3 3 1 2
  | 3 => tabC55 2 3 3 1 3
  | 4 => tabC55 2 3 3 1 4
  | 5 => tabC55 2 3 3 2 0
  | 6 => tabC55 2 3 3 2 1
  | 7 => tabC55 2 3 3 2 2
  | 8 => tabC55 2 3 3 2 3
  | 9 => tabC55 2 3 3 2 4
  | 10 => tabC55 2 3 3 3 0
  | 11 => tabC55 2 3 3 3 1
  | 12 => tabC55 2 3 3 3 2
  | 13 => tabC55 2 3 3 3 3
  | 14 => tabC55 2 3 3 3 4
  | 15 => tabC55 2 3 3 4 0
  | 16 => tabC55 2 3 3 4 1
  | 17 => tabC55 2 3 3 4 2
  | 18 => tabC55 2 3 3 4 3
  | 19 => tabC55 2 3 3 4 4
  | 20 => tabC55 2 3 4 0 0
  | 21 => tabC55 2 3 4 0 1
  | 22 => tabC55 2 3 4 0 2
  | 23 => tabC55 2 3 4 0 3
  | 24 => tabC55 2 3 4 0 4
  | 25 => tabC55 2 3 4 1 0
  | 26 => tabC55 2 3 4 1 1
  | 27 => tabC55 2 3 4 1 2
  | 28 => tabC55 2 3 4 1 3
  | 29 => tabC55 2 3 4 1 4
  | 30 => tabC55 2 3 4 2 0
  | 31 => tabC55 2 3 4 2 1
  | 32 => tabC55 2 3 4 2 2
  | 33 => tabC55 2 3 4 2 3
  | 34 => tabC55 2 3 4 2 4
  | 35 => tabC55 2 3 4 3 0
  | 36 => tabC55 2 3 4 3 1
  | 37 => tabC55 2 3 4 3 2
  | 38 => tabC55 2 3 4 3 3
  | 39 => tabC55 2 3 4 3 4
  | 40 => tabC55 2 3 4 4 0
  | 41 => tabC55 2 3 4 4 1
  | 42 => tabC55 2 3 4 4 2
  | 43 => tabC55 2 3 4 4 3
  | 44 => tabC55 2 3 4 4 4
  | 45 => tabC55 2 4 0 0 0
  | 46 => tabC55 2 4 0 0 1
  | 47 => tabC55 2 4 0 0 2
  | 48 => tabC55 2 4 0 0 3
  | 49 => tabC55 2 4 0 0 4
  | 50 => tabC55 2 4 0 1 0
  | 51 => tabC55 2 4 0 1 1
  | 52 => tabC55 2 4 0 1 2
  | 53 => tabC55 2 4 0 1 3
  | 54 => tabC55 2 4 0 1 4
  | _ => tabC55 2 4 0 2 0
def memRowC5531 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 4 0 2 1
  | 1 => tabC55 2 4 0 2 2
  | 2 => tabC55 2 4 0 2 3
  | 3 => tabC55 2 4 0 2 4
  | 4 => tabC55 2 4 0 3 0
  | 5 => tabC55 2 4 0 3 1
  | 6 => tabC55 2 4 0 3 2
  | 7 => tabC55 2 4 0 3 3
  | 8 => tabC55 2 4 0 3 4
  | 9 => tabC55 2 4 0 4 0
  | 10 => tabC55 2 4 0 4 1
  | 11 => tabC55 2 4 0 4 2
  | 12 => tabC55 2 4 0 4 3
  | 13 => tabC55 2 4 0 4 4
  | 14 => tabC55 2 4 1 0 0
  | 15 => tabC55 2 4 1 0 1
  | 16 => tabC55 2 4 1 0 2
  | 17 => tabC55 2 4 1 0 3
  | 18 => tabC55 2 4 1 0 4
  | 19 => tabC55 2 4 1 1 0
  | 20 => tabC55 2 4 1 1 1
  | 21 => tabC55 2 4 1 1 2
  | 22 => tabC55 2 4 1 1 3
  | 23 => tabC55 2 4 1 1 4
  | 24 => tabC55 2 4 1 2 0
  | 25 => tabC55 2 4 1 2 1
  | 26 => tabC55 2 4 1 2 2
  | 27 => tabC55 2 4 1 2 3
  | 28 => tabC55 2 4 1 2 4
  | 29 => tabC55 2 4 1 3 0
  | 30 => tabC55 2 4 1 3 1
  | 31 => tabC55 2 4 1 3 2
  | 32 => tabC55 2 4 1 3 3
  | 33 => tabC55 2 4 1 3 4
  | 34 => tabC55 2 4 1 4 0
  | 35 => tabC55 2 4 1 4 1
  | 36 => tabC55 2 4 1 4 2
  | 37 => tabC55 2 4 1 4 3
  | 38 => tabC55 2 4 1 4 4
  | 39 => tabC55 2 4 2 0 0
  | 40 => tabC55 2 4 2 0 1
  | 41 => tabC55 2 4 2 0 2
  | 42 => tabC55 2 4 2 0 3
  | 43 => tabC55 2 4 2 0 4
  | 44 => tabC55 2 4 2 1 0
  | 45 => tabC55 2 4 2 1 1
  | 46 => tabC55 2 4 2 1 2
  | 47 => tabC55 2 4 2 1 3
  | 48 => tabC55 2 4 2 1 4
  | 49 => tabC55 2 4 2 2 0
  | 50 => tabC55 2 4 2 2 1
  | 51 => tabC55 2 4 2 2 2
  | 52 => tabC55 2 4 2 2 3
  | 53 => tabC55 2 4 2 2 4
  | 54 => tabC55 2 4 2 3 0
  | _ => tabC55 2 4 2 3 1
def memRowC5532 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 4 2 3 2
  | 1 => tabC55 2 4 2 3 3
  | 2 => tabC55 2 4 2 3 4
  | 3 => tabC55 2 4 2 4 0
  | 4 => tabC55 2 4 2 4 1
  | 5 => tabC55 2 4 2 4 2
  | 6 => tabC55 2 4 2 4 3
  | 7 => tabC55 2 4 2 4 4
  | 8 => tabC55 2 4 3 0 0
  | 9 => tabC55 2 4 3 0 1
  | 10 => tabC55 2 4 3 0 2
  | 11 => tabC55 2 4 3 0 3
  | 12 => tabC55 2 4 3 0 4
  | 13 => tabC55 2 4 3 1 0
  | 14 => tabC55 2 4 3 1 1
  | 15 => tabC55 2 4 3 1 2
  | 16 => tabC55 2 4 3 1 3
  | 17 => tabC55 2 4 3 1 4
  | 18 => tabC55 2 4 3 2 0
  | 19 => tabC55 2 4 3 2 1
  | 20 => tabC55 2 4 3 2 2
  | 21 => tabC55 2 4 3 2 3
  | 22 => tabC55 2 4 3 2 4
  | 23 => tabC55 2 4 3 3 0
  | 24 => tabC55 2 4 3 3 1
  | 25 => tabC55 2 4 3 3 2
  | 26 => tabC55 2 4 3 3 3
  | 27 => tabC55 2 4 3 3 4
  | 28 => tabC55 2 4 3 4 0
  | 29 => tabC55 2 4 3 4 1
  | 30 => tabC55 2 4 3 4 2
  | 31 => tabC55 2 4 3 4 3
  | 32 => tabC55 2 4 3 4 4
  | 33 => tabC55 2 4 4 0 0
  | 34 => tabC55 2 4 4 0 1
  | 35 => tabC55 2 4 4 0 2
  | 36 => tabC55 2 4 4 0 3
  | 37 => tabC55 2 4 4 0 4
  | 38 => tabC55 2 4 4 1 0
  | 39 => tabC55 2 4 4 1 1
  | 40 => tabC55 2 4 4 1 2
  | 41 => tabC55 2 4 4 1 3
  | 42 => tabC55 2 4 4 1 4
  | 43 => tabC55 2 4 4 2 0
  | 44 => tabC55 2 4 4 2 1
  | 45 => tabC55 2 4 4 2 2
  | 46 => tabC55 2 4 4 2 3
  | 47 => tabC55 2 4 4 2 4
  | 48 => tabC55 2 4 4 3 0
  | 49 => tabC55 2 4 4 3 1
  | 50 => tabC55 2 4 4 3 2
  | 51 => tabC55 2 4 4 3 3
  | 52 => tabC55 2 4 4 3 4
  | 53 => tabC55 2 4 4 4 0
  | 54 => tabC55 2 4 4 4 1
  | _ => tabC55 2 4 4 4 2
def memRowC5533 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 2 4 4 4 3
  | 1 => tabC55 2 4 4 4 4
  | 2 => tabC55 3 0 0 0 0
  | 3 => tabC55 3 0 0 0 1
  | 4 => tabC55 3 0 0 0 2
  | 5 => tabC55 3 0 0 0 3
  | 6 => tabC55 3 0 0 0 4
  | 7 => tabC55 3 0 0 1 0
  | 8 => tabC55 3 0 0 1 1
  | 9 => tabC55 3 0 0 1 2
  | 10 => tabC55 3 0 0 1 3
  | 11 => tabC55 3 0 0 1 4
  | 12 => tabC55 3 0 0 2 0
  | 13 => tabC55 3 0 0 2 1
  | 14 => tabC55 3 0 0 2 2
  | 15 => tabC55 3 0 0 2 3
  | 16 => tabC55 3 0 0 2 4
  | 17 => tabC55 3 0 0 3 0
  | 18 => tabC55 3 0 0 3 1
  | 19 => tabC55 3 0 0 3 2
  | 20 => tabC55 3 0 0 3 3
  | 21 => tabC55 3 0 0 3 4
  | 22 => tabC55 3 0 0 4 0
  | 23 => tabC55 3 0 0 4 1
  | 24 => tabC55 3 0 0 4 2
  | 25 => tabC55 3 0 0 4 3
  | 26 => tabC55 3 0 0 4 4
  | 27 => tabC55 3 0 1 0 0
  | 28 => tabC55 3 0 1 0 1
  | 29 => tabC55 3 0 1 0 2
  | 30 => tabC55 3 0 1 0 3
  | 31 => tabC55 3 0 1 0 4
  | 32 => tabC55 3 0 1 1 0
  | 33 => tabC55 3 0 1 1 1
  | 34 => tabC55 3 0 1 1 2
  | 35 => tabC55 3 0 1 1 3
  | 36 => tabC55 3 0 1 1 4
  | 37 => tabC55 3 0 1 2 0
  | 38 => tabC55 3 0 1 2 1
  | 39 => tabC55 3 0 1 2 2
  | 40 => tabC55 3 0 1 2 3
  | 41 => tabC55 3 0 1 2 4
  | 42 => tabC55 3 0 1 3 0
  | 43 => tabC55 3 0 1 3 1
  | 44 => tabC55 3 0 1 3 2
  | 45 => tabC55 3 0 1 3 3
  | 46 => tabC55 3 0 1 3 4
  | 47 => tabC55 3 0 1 4 0
  | 48 => tabC55 3 0 1 4 1
  | 49 => tabC55 3 0 1 4 2
  | 50 => tabC55 3 0 1 4 3
  | 51 => tabC55 3 0 1 4 4
  | 52 => tabC55 3 0 2 0 0
  | 53 => tabC55 3 0 2 0 1
  | 54 => tabC55 3 0 2 0 2
  | _ => tabC55 3 0 2 0 3
def memRowC5534 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 0 2 0 4
  | 1 => tabC55 3 0 2 1 0
  | 2 => tabC55 3 0 2 1 1
  | 3 => tabC55 3 0 2 1 2
  | 4 => tabC55 3 0 2 1 3
  | 5 => tabC55 3 0 2 1 4
  | 6 => tabC55 3 0 2 2 0
  | 7 => tabC55 3 0 2 2 1
  | 8 => tabC55 3 0 2 2 2
  | 9 => tabC55 3 0 2 2 3
  | 10 => tabC55 3 0 2 2 4
  | 11 => tabC55 3 0 2 3 0
  | 12 => tabC55 3 0 2 3 1
  | 13 => tabC55 3 0 2 3 2
  | 14 => tabC55 3 0 2 3 3
  | 15 => tabC55 3 0 2 3 4
  | 16 => tabC55 3 0 2 4 0
  | 17 => tabC55 3 0 2 4 1
  | 18 => tabC55 3 0 2 4 2
  | 19 => tabC55 3 0 2 4 3
  | 20 => tabC55 3 0 2 4 4
  | 21 => tabC55 3 0 3 0 0
  | 22 => tabC55 3 0 3 0 1
  | 23 => tabC55 3 0 3 0 2
  | 24 => tabC55 3 0 3 0 3
  | 25 => tabC55 3 0 3 0 4
  | 26 => tabC55 3 0 3 1 0
  | 27 => tabC55 3 0 3 1 1
  | 28 => tabC55 3 0 3 1 2
  | 29 => tabC55 3 0 3 1 3
  | 30 => tabC55 3 0 3 1 4
  | 31 => tabC55 3 0 3 2 0
  | 32 => tabC55 3 0 3 2 1
  | 33 => tabC55 3 0 3 2 2
  | 34 => tabC55 3 0 3 2 3
  | 35 => tabC55 3 0 3 2 4
  | 36 => tabC55 3 0 3 3 0
  | 37 => tabC55 3 0 3 3 1
  | 38 => tabC55 3 0 3 3 2
  | 39 => tabC55 3 0 3 3 3
  | 40 => tabC55 3 0 3 3 4
  | 41 => tabC55 3 0 3 4 0
  | 42 => tabC55 3 0 3 4 1
  | 43 => tabC55 3 0 3 4 2
  | 44 => tabC55 3 0 3 4 3
  | 45 => tabC55 3 0 3 4 4
  | 46 => tabC55 3 0 4 0 0
  | 47 => tabC55 3 0 4 0 1
  | 48 => tabC55 3 0 4 0 2
  | 49 => tabC55 3 0 4 0 3
  | 50 => tabC55 3 0 4 0 4
  | 51 => tabC55 3 0 4 1 0
  | 52 => tabC55 3 0 4 1 1
  | 53 => tabC55 3 0 4 1 2
  | 54 => tabC55 3 0 4 1 3
  | _ => tabC55 3 0 4 1 4
def memRowC5535 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 0 4 2 0
  | 1 => tabC55 3 0 4 2 1
  | 2 => tabC55 3 0 4 2 2
  | 3 => tabC55 3 0 4 2 3
  | 4 => tabC55 3 0 4 2 4
  | 5 => tabC55 3 0 4 3 0
  | 6 => tabC55 3 0 4 3 1
  | 7 => tabC55 3 0 4 3 2
  | 8 => tabC55 3 0 4 3 3
  | 9 => tabC55 3 0 4 3 4
  | 10 => tabC55 3 0 4 4 0
  | 11 => tabC55 3 0 4 4 1
  | 12 => tabC55 3 0 4 4 2
  | 13 => tabC55 3 0 4 4 3
  | 14 => tabC55 3 0 4 4 4
  | 15 => tabC55 3 1 0 0 0
  | 16 => tabC55 3 1 0 0 1
  | 17 => tabC55 3 1 0 0 2
  | 18 => tabC55 3 1 0 0 3
  | 19 => tabC55 3 1 0 0 4
  | 20 => tabC55 3 1 0 1 0
  | 21 => tabC55 3 1 0 1 1
  | 22 => tabC55 3 1 0 1 2
  | 23 => tabC55 3 1 0 1 3
  | 24 => tabC55 3 1 0 1 4
  | 25 => tabC55 3 1 0 2 0
  | 26 => tabC55 3 1 0 2 1
  | 27 => tabC55 3 1 0 2 2
  | 28 => tabC55 3 1 0 2 3
  | 29 => tabC55 3 1 0 2 4
  | 30 => tabC55 3 1 0 3 0
  | 31 => tabC55 3 1 0 3 1
  | 32 => tabC55 3 1 0 3 2
  | 33 => tabC55 3 1 0 3 3
  | 34 => tabC55 3 1 0 3 4
  | 35 => tabC55 3 1 0 4 0
  | 36 => tabC55 3 1 0 4 1
  | 37 => tabC55 3 1 0 4 2
  | 38 => tabC55 3 1 0 4 3
  | 39 => tabC55 3 1 0 4 4
  | 40 => tabC55 3 1 1 0 0
  | 41 => tabC55 3 1 1 0 1
  | 42 => tabC55 3 1 1 0 2
  | 43 => tabC55 3 1 1 0 3
  | 44 => tabC55 3 1 1 0 4
  | 45 => tabC55 3 1 1 1 0
  | 46 => tabC55 3 1 1 1 1
  | 47 => tabC55 3 1 1 1 2
  | 48 => tabC55 3 1 1 1 3
  | 49 => tabC55 3 1 1 1 4
  | 50 => tabC55 3 1 1 2 0
  | 51 => tabC55 3 1 1 2 1
  | 52 => tabC55 3 1 1 2 2
  | 53 => tabC55 3 1 1 2 3
  | 54 => tabC55 3 1 1 2 4
  | _ => tabC55 3 1 1 3 0
def memRowC5536 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 1 1 3 1
  | 1 => tabC55 3 1 1 3 2
  | 2 => tabC55 3 1 1 3 3
  | 3 => tabC55 3 1 1 3 4
  | 4 => tabC55 3 1 1 4 0
  | 5 => tabC55 3 1 1 4 1
  | 6 => tabC55 3 1 1 4 2
  | 7 => tabC55 3 1 1 4 3
  | 8 => tabC55 3 1 1 4 4
  | 9 => tabC55 3 1 2 0 0
  | 10 => tabC55 3 1 2 0 1
  | 11 => tabC55 3 1 2 0 2
  | 12 => tabC55 3 1 2 0 3
  | 13 => tabC55 3 1 2 0 4
  | 14 => tabC55 3 1 2 1 0
  | 15 => tabC55 3 1 2 1 1
  | 16 => tabC55 3 1 2 1 2
  | 17 => tabC55 3 1 2 1 3
  | 18 => tabC55 3 1 2 1 4
  | 19 => tabC55 3 1 2 2 0
  | 20 => tabC55 3 1 2 2 1
  | 21 => tabC55 3 1 2 2 2
  | 22 => tabC55 3 1 2 2 3
  | 23 => tabC55 3 1 2 2 4
  | 24 => tabC55 3 1 2 3 0
  | 25 => tabC55 3 1 2 3 1
  | 26 => tabC55 3 1 2 3 2
  | 27 => tabC55 3 1 2 3 3
  | 28 => tabC55 3 1 2 3 4
  | 29 => tabC55 3 1 2 4 0
  | 30 => tabC55 3 1 2 4 1
  | 31 => tabC55 3 1 2 4 2
  | 32 => tabC55 3 1 2 4 3
  | 33 => tabC55 3 1 2 4 4
  | 34 => tabC55 3 1 3 0 0
  | 35 => tabC55 3 1 3 0 1
  | 36 => tabC55 3 1 3 0 2
  | 37 => tabC55 3 1 3 0 3
  | 38 => tabC55 3 1 3 0 4
  | 39 => tabC55 3 1 3 1 0
  | 40 => tabC55 3 1 3 1 1
  | 41 => tabC55 3 1 3 1 2
  | 42 => tabC55 3 1 3 1 3
  | 43 => tabC55 3 1 3 1 4
  | 44 => tabC55 3 1 3 2 0
  | 45 => tabC55 3 1 3 2 1
  | 46 => tabC55 3 1 3 2 2
  | 47 => tabC55 3 1 3 2 3
  | 48 => tabC55 3 1 3 2 4
  | 49 => tabC55 3 1 3 3 0
  | 50 => tabC55 3 1 3 3 1
  | 51 => tabC55 3 1 3 3 2
  | 52 => tabC55 3 1 3 3 3
  | 53 => tabC55 3 1 3 3 4
  | 54 => tabC55 3 1 3 4 0
  | _ => tabC55 3 1 3 4 1
def memRowC5537 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 1 3 4 2
  | 1 => tabC55 3 1 3 4 3
  | 2 => tabC55 3 1 3 4 4
  | 3 => tabC55 3 1 4 0 0
  | 4 => tabC55 3 1 4 0 1
  | 5 => tabC55 3 1 4 0 2
  | 6 => tabC55 3 1 4 0 3
  | 7 => tabC55 3 1 4 0 4
  | 8 => tabC55 3 1 4 1 0
  | 9 => tabC55 3 1 4 1 1
  | 10 => tabC55 3 1 4 1 2
  | 11 => tabC55 3 1 4 1 3
  | 12 => tabC55 3 1 4 1 4
  | 13 => tabC55 3 1 4 2 0
  | 14 => tabC55 3 1 4 2 1
  | 15 => tabC55 3 1 4 2 2
  | 16 => tabC55 3 1 4 2 3
  | 17 => tabC55 3 1 4 2 4
  | 18 => tabC55 3 1 4 3 0
  | 19 => tabC55 3 1 4 3 1
  | 20 => tabC55 3 1 4 3 2
  | 21 => tabC55 3 1 4 3 3
  | 22 => tabC55 3 1 4 3 4
  | 23 => tabC55 3 1 4 4 0
  | 24 => tabC55 3 1 4 4 1
  | 25 => tabC55 3 1 4 4 2
  | 26 => tabC55 3 1 4 4 3
  | 27 => tabC55 3 1 4 4 4
  | 28 => tabC55 3 2 0 0 0
  | 29 => tabC55 3 2 0 0 1
  | 30 => tabC55 3 2 0 0 2
  | 31 => tabC55 3 2 0 0 3
  | 32 => tabC55 3 2 0 0 4
  | 33 => tabC55 3 2 0 1 0
  | 34 => tabC55 3 2 0 1 1
  | 35 => tabC55 3 2 0 1 2
  | 36 => tabC55 3 2 0 1 3
  | 37 => tabC55 3 2 0 1 4
  | 38 => tabC55 3 2 0 2 0
  | 39 => tabC55 3 2 0 2 1
  | 40 => tabC55 3 2 0 2 2
  | 41 => tabC55 3 2 0 2 3
  | 42 => tabC55 3 2 0 2 4
  | 43 => tabC55 3 2 0 3 0
  | 44 => tabC55 3 2 0 3 1
  | 45 => tabC55 3 2 0 3 2
  | 46 => tabC55 3 2 0 3 3
  | 47 => tabC55 3 2 0 3 4
  | 48 => tabC55 3 2 0 4 0
  | 49 => tabC55 3 2 0 4 1
  | 50 => tabC55 3 2 0 4 2
  | 51 => tabC55 3 2 0 4 3
  | 52 => tabC55 3 2 0 4 4
  | 53 => tabC55 3 2 1 0 0
  | 54 => tabC55 3 2 1 0 1
  | _ => tabC55 3 2 1 0 2
def memRowC5538 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 2 1 0 3
  | 1 => tabC55 3 2 1 0 4
  | 2 => tabC55 3 2 1 1 0
  | 3 => tabC55 3 2 1 1 1
  | 4 => tabC55 3 2 1 1 2
  | 5 => tabC55 3 2 1 1 3
  | 6 => tabC55 3 2 1 1 4
  | 7 => tabC55 3 2 1 2 0
  | 8 => tabC55 3 2 1 2 1
  | 9 => tabC55 3 2 1 2 2
  | 10 => tabC55 3 2 1 2 3
  | 11 => tabC55 3 2 1 2 4
  | 12 => tabC55 3 2 1 3 0
  | 13 => tabC55 3 2 1 3 1
  | 14 => tabC55 3 2 1 3 2
  | 15 => tabC55 3 2 1 3 3
  | 16 => tabC55 3 2 1 3 4
  | 17 => tabC55 3 2 1 4 0
  | 18 => tabC55 3 2 1 4 1
  | 19 => tabC55 3 2 1 4 2
  | 20 => tabC55 3 2 1 4 3
  | 21 => tabC55 3 2 1 4 4
  | 22 => tabC55 3 2 2 0 0
  | 23 => tabC55 3 2 2 0 1
  | 24 => tabC55 3 2 2 0 2
  | 25 => tabC55 3 2 2 0 3
  | 26 => tabC55 3 2 2 0 4
  | 27 => tabC55 3 2 2 1 0
  | 28 => tabC55 3 2 2 1 1
  | 29 => tabC55 3 2 2 1 2
  | 30 => tabC55 3 2 2 1 3
  | 31 => tabC55 3 2 2 1 4
  | 32 => tabC55 3 2 2 2 0
  | 33 => tabC55 3 2 2 2 1
  | 34 => tabC55 3 2 2 2 2
  | 35 => tabC55 3 2 2 2 3
  | 36 => tabC55 3 2 2 2 4
  | 37 => tabC55 3 2 2 3 0
  | 38 => tabC55 3 2 2 3 1
  | 39 => tabC55 3 2 2 3 2
  | 40 => tabC55 3 2 2 3 3
  | 41 => tabC55 3 2 2 3 4
  | 42 => tabC55 3 2 2 4 0
  | 43 => tabC55 3 2 2 4 1
  | 44 => tabC55 3 2 2 4 2
  | 45 => tabC55 3 2 2 4 3
  | 46 => tabC55 3 2 2 4 4
  | 47 => tabC55 3 2 3 0 0
  | 48 => tabC55 3 2 3 0 1
  | 49 => tabC55 3 2 3 0 2
  | 50 => tabC55 3 2 3 0 3
  | 51 => tabC55 3 2 3 0 4
  | 52 => tabC55 3 2 3 1 0
  | 53 => tabC55 3 2 3 1 1
  | 54 => tabC55 3 2 3 1 2
  | _ => tabC55 3 2 3 1 3
def memRowC5539 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 2 3 1 4
  | 1 => tabC55 3 2 3 2 0
  | 2 => tabC55 3 2 3 2 1
  | 3 => tabC55 3 2 3 2 2
  | 4 => tabC55 3 2 3 2 3
  | 5 => tabC55 3 2 3 2 4
  | 6 => tabC55 3 2 3 3 0
  | 7 => tabC55 3 2 3 3 1
  | 8 => tabC55 3 2 3 3 2
  | 9 => tabC55 3 2 3 3 3
  | 10 => tabC55 3 2 3 3 4
  | 11 => tabC55 3 2 3 4 0
  | 12 => tabC55 3 2 3 4 1
  | 13 => tabC55 3 2 3 4 2
  | 14 => tabC55 3 2 3 4 3
  | 15 => tabC55 3 2 3 4 4
  | 16 => tabC55 3 2 4 0 0
  | 17 => tabC55 3 2 4 0 1
  | 18 => tabC55 3 2 4 0 2
  | 19 => tabC55 3 2 4 0 3
  | 20 => tabC55 3 2 4 0 4
  | 21 => tabC55 3 2 4 1 0
  | 22 => tabC55 3 2 4 1 1
  | 23 => tabC55 3 2 4 1 2
  | 24 => tabC55 3 2 4 1 3
  | 25 => tabC55 3 2 4 1 4
  | 26 => tabC55 3 2 4 2 0
  | 27 => tabC55 3 2 4 2 1
  | 28 => tabC55 3 2 4 2 2
  | 29 => tabC55 3 2 4 2 3
  | 30 => tabC55 3 2 4 2 4
  | 31 => tabC55 3 2 4 3 0
  | 32 => tabC55 3 2 4 3 1
  | 33 => tabC55 3 2 4 3 2
  | 34 => tabC55 3 2 4 3 3
  | 35 => tabC55 3 2 4 3 4
  | 36 => tabC55 3 2 4 4 0
  | 37 => tabC55 3 2 4 4 1
  | 38 => tabC55 3 2 4 4 2
  | 39 => tabC55 3 2 4 4 3
  | 40 => tabC55 3 2 4 4 4
  | 41 => tabC55 3 3 0 0 0
  | 42 => tabC55 3 3 0 0 1
  | 43 => tabC55 3 3 0 0 2
  | 44 => tabC55 3 3 0 0 3
  | 45 => tabC55 3 3 0 0 4
  | 46 => tabC55 3 3 0 1 0
  | 47 => tabC55 3 3 0 1 1
  | 48 => tabC55 3 3 0 1 2
  | 49 => tabC55 3 3 0 1 3
  | 50 => tabC55 3 3 0 1 4
  | 51 => tabC55 3 3 0 2 0
  | 52 => tabC55 3 3 0 2 1
  | 53 => tabC55 3 3 0 2 2
  | 54 => tabC55 3 3 0 2 3
  | _ => tabC55 3 3 0 2 4
def memRowC5540 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 3 0 3 0
  | 1 => tabC55 3 3 0 3 1
  | 2 => tabC55 3 3 0 3 2
  | 3 => tabC55 3 3 0 3 3
  | 4 => tabC55 3 3 0 3 4
  | 5 => tabC55 3 3 0 4 0
  | 6 => tabC55 3 3 0 4 1
  | 7 => tabC55 3 3 0 4 2
  | 8 => tabC55 3 3 0 4 3
  | 9 => tabC55 3 3 0 4 4
  | 10 => tabC55 3 3 1 0 0
  | 11 => tabC55 3 3 1 0 1
  | 12 => tabC55 3 3 1 0 2
  | 13 => tabC55 3 3 1 0 3
  | 14 => tabC55 3 3 1 0 4
  | 15 => tabC55 3 3 1 1 0
  | 16 => tabC55 3 3 1 1 1
  | 17 => tabC55 3 3 1 1 2
  | 18 => tabC55 3 3 1 1 3
  | 19 => tabC55 3 3 1 1 4
  | 20 => tabC55 3 3 1 2 0
  | 21 => tabC55 3 3 1 2 1
  | 22 => tabC55 3 3 1 2 2
  | 23 => tabC55 3 3 1 2 3
  | 24 => tabC55 3 3 1 2 4
  | 25 => tabC55 3 3 1 3 0
  | 26 => tabC55 3 3 1 3 1
  | 27 => tabC55 3 3 1 3 2
  | 28 => tabC55 3 3 1 3 3
  | 29 => tabC55 3 3 1 3 4
  | 30 => tabC55 3 3 1 4 0
  | 31 => tabC55 3 3 1 4 1
  | 32 => tabC55 3 3 1 4 2
  | 33 => tabC55 3 3 1 4 3
  | 34 => tabC55 3 3 1 4 4
  | 35 => tabC55 3 3 2 0 0
  | 36 => tabC55 3 3 2 0 1
  | 37 => tabC55 3 3 2 0 2
  | 38 => tabC55 3 3 2 0 3
  | 39 => tabC55 3 3 2 0 4
  | 40 => tabC55 3 3 2 1 0
  | 41 => tabC55 3 3 2 1 1
  | 42 => tabC55 3 3 2 1 2
  | 43 => tabC55 3 3 2 1 3
  | 44 => tabC55 3 3 2 1 4
  | 45 => tabC55 3 3 2 2 0
  | 46 => tabC55 3 3 2 2 1
  | 47 => tabC55 3 3 2 2 2
  | 48 => tabC55 3 3 2 2 3
  | 49 => tabC55 3 3 2 2 4
  | 50 => tabC55 3 3 2 3 0
  | 51 => tabC55 3 3 2 3 1
  | 52 => tabC55 3 3 2 3 2
  | 53 => tabC55 3 3 2 3 3
  | 54 => tabC55 3 3 2 3 4
  | _ => tabC55 3 3 2 4 0
def memRowC5541 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 3 2 4 1
  | 1 => tabC55 3 3 2 4 2
  | 2 => tabC55 3 3 2 4 3
  | 3 => tabC55 3 3 2 4 4
  | 4 => tabC55 3 3 3 0 0
  | 5 => tabC55 3 3 3 0 1
  | 6 => tabC55 3 3 3 0 2
  | 7 => tabC55 3 3 3 0 3
  | 8 => tabC55 3 3 3 0 4
  | 9 => tabC55 3 3 3 1 0
  | 10 => tabC55 3 3 3 1 1
  | 11 => tabC55 3 3 3 1 2
  | 12 => tabC55 3 3 3 1 3
  | 13 => tabC55 3 3 3 1 4
  | 14 => tabC55 3 3 3 2 0
  | 15 => tabC55 3 3 3 2 1
  | 16 => tabC55 3 3 3 2 2
  | 17 => tabC55 3 3 3 2 3
  | 18 => tabC55 3 3 3 2 4
  | 19 => tabC55 3 3 3 3 0
  | 20 => tabC55 3 3 3 3 1
  | 21 => tabC55 3 3 3 3 2
  | 22 => tabC55 3 3 3 3 3
  | 23 => tabC55 3 3 3 3 4
  | 24 => tabC55 3 3 3 4 0
  | 25 => tabC55 3 3 3 4 1
  | 26 => tabC55 3 3 3 4 2
  | 27 => tabC55 3 3 3 4 3
  | 28 => tabC55 3 3 3 4 4
  | 29 => tabC55 3 3 4 0 0
  | 30 => tabC55 3 3 4 0 1
  | 31 => tabC55 3 3 4 0 2
  | 32 => tabC55 3 3 4 0 3
  | 33 => tabC55 3 3 4 0 4
  | 34 => tabC55 3 3 4 1 0
  | 35 => tabC55 3 3 4 1 1
  | 36 => tabC55 3 3 4 1 2
  | 37 => tabC55 3 3 4 1 3
  | 38 => tabC55 3 3 4 1 4
  | 39 => tabC55 3 3 4 2 0
  | 40 => tabC55 3 3 4 2 1
  | 41 => tabC55 3 3 4 2 2
  | 42 => tabC55 3 3 4 2 3
  | 43 => tabC55 3 3 4 2 4
  | 44 => tabC55 3 3 4 3 0
  | 45 => tabC55 3 3 4 3 1
  | 46 => tabC55 3 3 4 3 2
  | 47 => tabC55 3 3 4 3 3
  | 48 => tabC55 3 3 4 3 4
  | 49 => tabC55 3 3 4 4 0
  | 50 => tabC55 3 3 4 4 1
  | 51 => tabC55 3 3 4 4 2
  | 52 => tabC55 3 3 4 4 3
  | 53 => tabC55 3 3 4 4 4
  | 54 => tabC55 3 4 0 0 0
  | _ => tabC55 3 4 0 0 1
def memRowC5542 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 4 0 0 2
  | 1 => tabC55 3 4 0 0 3
  | 2 => tabC55 3 4 0 0 4
  | 3 => tabC55 3 4 0 1 0
  | 4 => tabC55 3 4 0 1 1
  | 5 => tabC55 3 4 0 1 2
  | 6 => tabC55 3 4 0 1 3
  | 7 => tabC55 3 4 0 1 4
  | 8 => tabC55 3 4 0 2 0
  | 9 => tabC55 3 4 0 2 1
  | 10 => tabC55 3 4 0 2 2
  | 11 => tabC55 3 4 0 2 3
  | 12 => tabC55 3 4 0 2 4
  | 13 => tabC55 3 4 0 3 0
  | 14 => tabC55 3 4 0 3 1
  | 15 => tabC55 3 4 0 3 2
  | 16 => tabC55 3 4 0 3 3
  | 17 => tabC55 3 4 0 3 4
  | 18 => tabC55 3 4 0 4 0
  | 19 => tabC55 3 4 0 4 1
  | 20 => tabC55 3 4 0 4 2
  | 21 => tabC55 3 4 0 4 3
  | 22 => tabC55 3 4 0 4 4
  | 23 => tabC55 3 4 1 0 0
  | 24 => tabC55 3 4 1 0 1
  | 25 => tabC55 3 4 1 0 2
  | 26 => tabC55 3 4 1 0 3
  | 27 => tabC55 3 4 1 0 4
  | 28 => tabC55 3 4 1 1 0
  | 29 => tabC55 3 4 1 1 1
  | 30 => tabC55 3 4 1 1 2
  | 31 => tabC55 3 4 1 1 3
  | 32 => tabC55 3 4 1 1 4
  | 33 => tabC55 3 4 1 2 0
  | 34 => tabC55 3 4 1 2 1
  | 35 => tabC55 3 4 1 2 2
  | 36 => tabC55 3 4 1 2 3
  | 37 => tabC55 3 4 1 2 4
  | 38 => tabC55 3 4 1 3 0
  | 39 => tabC55 3 4 1 3 1
  | 40 => tabC55 3 4 1 3 2
  | 41 => tabC55 3 4 1 3 3
  | 42 => tabC55 3 4 1 3 4
  | 43 => tabC55 3 4 1 4 0
  | 44 => tabC55 3 4 1 4 1
  | 45 => tabC55 3 4 1 4 2
  | 46 => tabC55 3 4 1 4 3
  | 47 => tabC55 3 4 1 4 4
  | 48 => tabC55 3 4 2 0 0
  | 49 => tabC55 3 4 2 0 1
  | 50 => tabC55 3 4 2 0 2
  | 51 => tabC55 3 4 2 0 3
  | 52 => tabC55 3 4 2 0 4
  | 53 => tabC55 3 4 2 1 0
  | 54 => tabC55 3 4 2 1 1
  | _ => tabC55 3 4 2 1 2
def memRowC5543 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 4 2 1 3
  | 1 => tabC55 3 4 2 1 4
  | 2 => tabC55 3 4 2 2 0
  | 3 => tabC55 3 4 2 2 1
  | 4 => tabC55 3 4 2 2 2
  | 5 => tabC55 3 4 2 2 3
  | 6 => tabC55 3 4 2 2 4
  | 7 => tabC55 3 4 2 3 0
  | 8 => tabC55 3 4 2 3 1
  | 9 => tabC55 3 4 2 3 2
  | 10 => tabC55 3 4 2 3 3
  | 11 => tabC55 3 4 2 3 4
  | 12 => tabC55 3 4 2 4 0
  | 13 => tabC55 3 4 2 4 1
  | 14 => tabC55 3 4 2 4 2
  | 15 => tabC55 3 4 2 4 3
  | 16 => tabC55 3 4 2 4 4
  | 17 => tabC55 3 4 3 0 0
  | 18 => tabC55 3 4 3 0 1
  | 19 => tabC55 3 4 3 0 2
  | 20 => tabC55 3 4 3 0 3
  | 21 => tabC55 3 4 3 0 4
  | 22 => tabC55 3 4 3 1 0
  | 23 => tabC55 3 4 3 1 1
  | 24 => tabC55 3 4 3 1 2
  | 25 => tabC55 3 4 3 1 3
  | 26 => tabC55 3 4 3 1 4
  | 27 => tabC55 3 4 3 2 0
  | 28 => tabC55 3 4 3 2 1
  | 29 => tabC55 3 4 3 2 2
  | 30 => tabC55 3 4 3 2 3
  | 31 => tabC55 3 4 3 2 4
  | 32 => tabC55 3 4 3 3 0
  | 33 => tabC55 3 4 3 3 1
  | 34 => tabC55 3 4 3 3 2
  | 35 => tabC55 3 4 3 3 3
  | 36 => tabC55 3 4 3 3 4
  | 37 => tabC55 3 4 3 4 0
  | 38 => tabC55 3 4 3 4 1
  | 39 => tabC55 3 4 3 4 2
  | 40 => tabC55 3 4 3 4 3
  | 41 => tabC55 3 4 3 4 4
  | 42 => tabC55 3 4 4 0 0
  | 43 => tabC55 3 4 4 0 1
  | 44 => tabC55 3 4 4 0 2
  | 45 => tabC55 3 4 4 0 3
  | 46 => tabC55 3 4 4 0 4
  | 47 => tabC55 3 4 4 1 0
  | 48 => tabC55 3 4 4 1 1
  | 49 => tabC55 3 4 4 1 2
  | 50 => tabC55 3 4 4 1 3
  | 51 => tabC55 3 4 4 1 4
  | 52 => tabC55 3 4 4 2 0
  | 53 => tabC55 3 4 4 2 1
  | 54 => tabC55 3 4 4 2 2
  | _ => tabC55 3 4 4 2 3
def memRowC5544 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 3 4 4 2 4
  | 1 => tabC55 3 4 4 3 0
  | 2 => tabC55 3 4 4 3 1
  | 3 => tabC55 3 4 4 3 2
  | 4 => tabC55 3 4 4 3 3
  | 5 => tabC55 3 4 4 3 4
  | 6 => tabC55 3 4 4 4 0
  | 7 => tabC55 3 4 4 4 1
  | 8 => tabC55 3 4 4 4 2
  | 9 => tabC55 3 4 4 4 3
  | 10 => tabC55 3 4 4 4 4
  | 11 => tabC55 4 0 0 0 0
  | 12 => tabC55 4 0 0 0 1
  | 13 => tabC55 4 0 0 0 2
  | 14 => tabC55 4 0 0 0 3
  | 15 => tabC55 4 0 0 0 4
  | 16 => tabC55 4 0 0 1 0
  | 17 => tabC55 4 0 0 1 1
  | 18 => tabC55 4 0 0 1 2
  | 19 => tabC55 4 0 0 1 3
  | 20 => tabC55 4 0 0 1 4
  | 21 => tabC55 4 0 0 2 0
  | 22 => tabC55 4 0 0 2 1
  | 23 => tabC55 4 0 0 2 2
  | 24 => tabC55 4 0 0 2 3
  | 25 => tabC55 4 0 0 2 4
  | 26 => tabC55 4 0 0 3 0
  | 27 => tabC55 4 0 0 3 1
  | 28 => tabC55 4 0 0 3 2
  | 29 => tabC55 4 0 0 3 3
  | 30 => tabC55 4 0 0 3 4
  | 31 => tabC55 4 0 0 4 0
  | 32 => tabC55 4 0 0 4 1
  | 33 => tabC55 4 0 0 4 2
  | 34 => tabC55 4 0 0 4 3
  | 35 => tabC55 4 0 0 4 4
  | 36 => tabC55 4 0 1 0 0
  | 37 => tabC55 4 0 1 0 1
  | 38 => tabC55 4 0 1 0 2
  | 39 => tabC55 4 0 1 0 3
  | 40 => tabC55 4 0 1 0 4
  | 41 => tabC55 4 0 1 1 0
  | 42 => tabC55 4 0 1 1 1
  | 43 => tabC55 4 0 1 1 2
  | 44 => tabC55 4 0 1 1 3
  | 45 => tabC55 4 0 1 1 4
  | 46 => tabC55 4 0 1 2 0
  | 47 => tabC55 4 0 1 2 1
  | 48 => tabC55 4 0 1 2 2
  | 49 => tabC55 4 0 1 2 3
  | 50 => tabC55 4 0 1 2 4
  | 51 => tabC55 4 0 1 3 0
  | 52 => tabC55 4 0 1 3 1
  | 53 => tabC55 4 0 1 3 2
  | 54 => tabC55 4 0 1 3 3
  | _ => tabC55 4 0 1 3 4
def memRowC5545 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 0 1 4 0
  | 1 => tabC55 4 0 1 4 1
  | 2 => tabC55 4 0 1 4 2
  | 3 => tabC55 4 0 1 4 3
  | 4 => tabC55 4 0 1 4 4
  | 5 => tabC55 4 0 2 0 0
  | 6 => tabC55 4 0 2 0 1
  | 7 => tabC55 4 0 2 0 2
  | 8 => tabC55 4 0 2 0 3
  | 9 => tabC55 4 0 2 0 4
  | 10 => tabC55 4 0 2 1 0
  | 11 => tabC55 4 0 2 1 1
  | 12 => tabC55 4 0 2 1 2
  | 13 => tabC55 4 0 2 1 3
  | 14 => tabC55 4 0 2 1 4
  | 15 => tabC55 4 0 2 2 0
  | 16 => tabC55 4 0 2 2 1
  | 17 => tabC55 4 0 2 2 2
  | 18 => tabC55 4 0 2 2 3
  | 19 => tabC55 4 0 2 2 4
  | 20 => tabC55 4 0 2 3 0
  | 21 => tabC55 4 0 2 3 1
  | 22 => tabC55 4 0 2 3 2
  | 23 => tabC55 4 0 2 3 3
  | 24 => tabC55 4 0 2 3 4
  | 25 => tabC55 4 0 2 4 0
  | 26 => tabC55 4 0 2 4 1
  | 27 => tabC55 4 0 2 4 2
  | 28 => tabC55 4 0 2 4 3
  | 29 => tabC55 4 0 2 4 4
  | 30 => tabC55 4 0 3 0 0
  | 31 => tabC55 4 0 3 0 1
  | 32 => tabC55 4 0 3 0 2
  | 33 => tabC55 4 0 3 0 3
  | 34 => tabC55 4 0 3 0 4
  | 35 => tabC55 4 0 3 1 0
  | 36 => tabC55 4 0 3 1 1
  | 37 => tabC55 4 0 3 1 2
  | 38 => tabC55 4 0 3 1 3
  | 39 => tabC55 4 0 3 1 4
  | 40 => tabC55 4 0 3 2 0
  | 41 => tabC55 4 0 3 2 1
  | 42 => tabC55 4 0 3 2 2
  | 43 => tabC55 4 0 3 2 3
  | 44 => tabC55 4 0 3 2 4
  | 45 => tabC55 4 0 3 3 0
  | 46 => tabC55 4 0 3 3 1
  | 47 => tabC55 4 0 3 3 2
  | 48 => tabC55 4 0 3 3 3
  | 49 => tabC55 4 0 3 3 4
  | 50 => tabC55 4 0 3 4 0
  | 51 => tabC55 4 0 3 4 1
  | 52 => tabC55 4 0 3 4 2
  | 53 => tabC55 4 0 3 4 3
  | 54 => tabC55 4 0 3 4 4
  | _ => tabC55 4 0 4 0 0
def memRowC5546 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 0 4 0 1
  | 1 => tabC55 4 0 4 0 2
  | 2 => tabC55 4 0 4 0 3
  | 3 => tabC55 4 0 4 0 4
  | 4 => tabC55 4 0 4 1 0
  | 5 => tabC55 4 0 4 1 1
  | 6 => tabC55 4 0 4 1 2
  | 7 => tabC55 4 0 4 1 3
  | 8 => tabC55 4 0 4 1 4
  | 9 => tabC55 4 0 4 2 0
  | 10 => tabC55 4 0 4 2 1
  | 11 => tabC55 4 0 4 2 2
  | 12 => tabC55 4 0 4 2 3
  | 13 => tabC55 4 0 4 2 4
  | 14 => tabC55 4 0 4 3 0
  | 15 => tabC55 4 0 4 3 1
  | 16 => tabC55 4 0 4 3 2
  | 17 => tabC55 4 0 4 3 3
  | 18 => tabC55 4 0 4 3 4
  | 19 => tabC55 4 0 4 4 0
  | 20 => tabC55 4 0 4 4 1
  | 21 => tabC55 4 0 4 4 2
  | 22 => tabC55 4 0 4 4 3
  | 23 => tabC55 4 0 4 4 4
  | 24 => tabC55 4 1 0 0 0
  | 25 => tabC55 4 1 0 0 1
  | 26 => tabC55 4 1 0 0 2
  | 27 => tabC55 4 1 0 0 3
  | 28 => tabC55 4 1 0 0 4
  | 29 => tabC55 4 1 0 1 0
  | 30 => tabC55 4 1 0 1 1
  | 31 => tabC55 4 1 0 1 2
  | 32 => tabC55 4 1 0 1 3
  | 33 => tabC55 4 1 0 1 4
  | 34 => tabC55 4 1 0 2 0
  | 35 => tabC55 4 1 0 2 1
  | 36 => tabC55 4 1 0 2 2
  | 37 => tabC55 4 1 0 2 3
  | 38 => tabC55 4 1 0 2 4
  | 39 => tabC55 4 1 0 3 0
  | 40 => tabC55 4 1 0 3 1
  | 41 => tabC55 4 1 0 3 2
  | 42 => tabC55 4 1 0 3 3
  | 43 => tabC55 4 1 0 3 4
  | 44 => tabC55 4 1 0 4 0
  | 45 => tabC55 4 1 0 4 1
  | 46 => tabC55 4 1 0 4 2
  | 47 => tabC55 4 1 0 4 3
  | 48 => tabC55 4 1 0 4 4
  | 49 => tabC55 4 1 1 0 0
  | 50 => tabC55 4 1 1 0 1
  | 51 => tabC55 4 1 1 0 2
  | 52 => tabC55 4 1 1 0 3
  | 53 => tabC55 4 1 1 0 4
  | 54 => tabC55 4 1 1 1 0
  | _ => tabC55 4 1 1 1 1
def memRowC5547 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 1 1 1 2
  | 1 => tabC55 4 1 1 1 3
  | 2 => tabC55 4 1 1 1 4
  | 3 => tabC55 4 1 1 2 0
  | 4 => tabC55 4 1 1 2 1
  | 5 => tabC55 4 1 1 2 2
  | 6 => tabC55 4 1 1 2 3
  | 7 => tabC55 4 1 1 2 4
  | 8 => tabC55 4 1 1 3 0
  | 9 => tabC55 4 1 1 3 1
  | 10 => tabC55 4 1 1 3 2
  | 11 => tabC55 4 1 1 3 3
  | 12 => tabC55 4 1 1 3 4
  | 13 => tabC55 4 1 1 4 0
  | 14 => tabC55 4 1 1 4 1
  | 15 => tabC55 4 1 1 4 2
  | 16 => tabC55 4 1 1 4 3
  | 17 => tabC55 4 1 1 4 4
  | 18 => tabC55 4 1 2 0 0
  | 19 => tabC55 4 1 2 0 1
  | 20 => tabC55 4 1 2 0 2
  | 21 => tabC55 4 1 2 0 3
  | 22 => tabC55 4 1 2 0 4
  | 23 => tabC55 4 1 2 1 0
  | 24 => tabC55 4 1 2 1 1
  | 25 => tabC55 4 1 2 1 2
  | 26 => tabC55 4 1 2 1 3
  | 27 => tabC55 4 1 2 1 4
  | 28 => tabC55 4 1 2 2 0
  | 29 => tabC55 4 1 2 2 1
  | 30 => tabC55 4 1 2 2 2
  | 31 => tabC55 4 1 2 2 3
  | 32 => tabC55 4 1 2 2 4
  | 33 => tabC55 4 1 2 3 0
  | 34 => tabC55 4 1 2 3 1
  | 35 => tabC55 4 1 2 3 2
  | 36 => tabC55 4 1 2 3 3
  | 37 => tabC55 4 1 2 3 4
  | 38 => tabC55 4 1 2 4 0
  | 39 => tabC55 4 1 2 4 1
  | 40 => tabC55 4 1 2 4 2
  | 41 => tabC55 4 1 2 4 3
  | 42 => tabC55 4 1 2 4 4
  | 43 => tabC55 4 1 3 0 0
  | 44 => tabC55 4 1 3 0 1
  | 45 => tabC55 4 1 3 0 2
  | 46 => tabC55 4 1 3 0 3
  | 47 => tabC55 4 1 3 0 4
  | 48 => tabC55 4 1 3 1 0
  | 49 => tabC55 4 1 3 1 1
  | 50 => tabC55 4 1 3 1 2
  | 51 => tabC55 4 1 3 1 3
  | 52 => tabC55 4 1 3 1 4
  | 53 => tabC55 4 1 3 2 0
  | 54 => tabC55 4 1 3 2 1
  | _ => tabC55 4 1 3 2 2
def memRowC5548 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 1 3 2 3
  | 1 => tabC55 4 1 3 2 4
  | 2 => tabC55 4 1 3 3 0
  | 3 => tabC55 4 1 3 3 1
  | 4 => tabC55 4 1 3 3 2
  | 5 => tabC55 4 1 3 3 3
  | 6 => tabC55 4 1 3 3 4
  | 7 => tabC55 4 1 3 4 0
  | 8 => tabC55 4 1 3 4 1
  | 9 => tabC55 4 1 3 4 2
  | 10 => tabC55 4 1 3 4 3
  | 11 => tabC55 4 1 3 4 4
  | 12 => tabC55 4 1 4 0 0
  | 13 => tabC55 4 1 4 0 1
  | 14 => tabC55 4 1 4 0 2
  | 15 => tabC55 4 1 4 0 3
  | 16 => tabC55 4 1 4 0 4
  | 17 => tabC55 4 1 4 1 0
  | 18 => tabC55 4 1 4 1 1
  | 19 => tabC55 4 1 4 1 2
  | 20 => tabC55 4 1 4 1 3
  | 21 => tabC55 4 1 4 1 4
  | 22 => tabC55 4 1 4 2 0
  | 23 => tabC55 4 1 4 2 1
  | 24 => tabC55 4 1 4 2 2
  | 25 => tabC55 4 1 4 2 3
  | 26 => tabC55 4 1 4 2 4
  | 27 => tabC55 4 1 4 3 0
  | 28 => tabC55 4 1 4 3 1
  | 29 => tabC55 4 1 4 3 2
  | 30 => tabC55 4 1 4 3 3
  | 31 => tabC55 4 1 4 3 4
  | 32 => tabC55 4 1 4 4 0
  | 33 => tabC55 4 1 4 4 1
  | 34 => tabC55 4 1 4 4 2
  | 35 => tabC55 4 1 4 4 3
  | 36 => tabC55 4 1 4 4 4
  | 37 => tabC55 4 2 0 0 0
  | 38 => tabC55 4 2 0 0 1
  | 39 => tabC55 4 2 0 0 2
  | 40 => tabC55 4 2 0 0 3
  | 41 => tabC55 4 2 0 0 4
  | 42 => tabC55 4 2 0 1 0
  | 43 => tabC55 4 2 0 1 1
  | 44 => tabC55 4 2 0 1 2
  | 45 => tabC55 4 2 0 1 3
  | 46 => tabC55 4 2 0 1 4
  | 47 => tabC55 4 2 0 2 0
  | 48 => tabC55 4 2 0 2 1
  | 49 => tabC55 4 2 0 2 2
  | 50 => tabC55 4 2 0 2 3
  | 51 => tabC55 4 2 0 2 4
  | 52 => tabC55 4 2 0 3 0
  | 53 => tabC55 4 2 0 3 1
  | 54 => tabC55 4 2 0 3 2
  | _ => tabC55 4 2 0 3 3
def memRowC5549 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 2 0 3 4
  | 1 => tabC55 4 2 0 4 0
  | 2 => tabC55 4 2 0 4 1
  | 3 => tabC55 4 2 0 4 2
  | 4 => tabC55 4 2 0 4 3
  | 5 => tabC55 4 2 0 4 4
  | 6 => tabC55 4 2 1 0 0
  | 7 => tabC55 4 2 1 0 1
  | 8 => tabC55 4 2 1 0 2
  | 9 => tabC55 4 2 1 0 3
  | 10 => tabC55 4 2 1 0 4
  | 11 => tabC55 4 2 1 1 0
  | 12 => tabC55 4 2 1 1 1
  | 13 => tabC55 4 2 1 1 2
  | 14 => tabC55 4 2 1 1 3
  | 15 => tabC55 4 2 1 1 4
  | 16 => tabC55 4 2 1 2 0
  | 17 => tabC55 4 2 1 2 1
  | 18 => tabC55 4 2 1 2 2
  | 19 => tabC55 4 2 1 2 3
  | 20 => tabC55 4 2 1 2 4
  | 21 => tabC55 4 2 1 3 0
  | 22 => tabC55 4 2 1 3 1
  | 23 => tabC55 4 2 1 3 2
  | 24 => tabC55 4 2 1 3 3
  | 25 => tabC55 4 2 1 3 4
  | 26 => tabC55 4 2 1 4 0
  | 27 => tabC55 4 2 1 4 1
  | 28 => tabC55 4 2 1 4 2
  | 29 => tabC55 4 2 1 4 3
  | 30 => tabC55 4 2 1 4 4
  | 31 => tabC55 4 2 2 0 0
  | 32 => tabC55 4 2 2 0 1
  | 33 => tabC55 4 2 2 0 2
  | 34 => tabC55 4 2 2 0 3
  | 35 => tabC55 4 2 2 0 4
  | 36 => tabC55 4 2 2 1 0
  | 37 => tabC55 4 2 2 1 1
  | 38 => tabC55 4 2 2 1 2
  | 39 => tabC55 4 2 2 1 3
  | 40 => tabC55 4 2 2 1 4
  | 41 => tabC55 4 2 2 2 0
  | 42 => tabC55 4 2 2 2 1
  | 43 => tabC55 4 2 2 2 2
  | 44 => tabC55 4 2 2 2 3
  | 45 => tabC55 4 2 2 2 4
  | 46 => tabC55 4 2 2 3 0
  | 47 => tabC55 4 2 2 3 1
  | 48 => tabC55 4 2 2 3 2
  | 49 => tabC55 4 2 2 3 3
  | 50 => tabC55 4 2 2 3 4
  | 51 => tabC55 4 2 2 4 0
  | 52 => tabC55 4 2 2 4 1
  | 53 => tabC55 4 2 2 4 2
  | 54 => tabC55 4 2 2 4 3
  | _ => tabC55 4 2 2 4 4
def memRowC5550 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 2 3 0 0
  | 1 => tabC55 4 2 3 0 1
  | 2 => tabC55 4 2 3 0 2
  | 3 => tabC55 4 2 3 0 3
  | 4 => tabC55 4 2 3 0 4
  | 5 => tabC55 4 2 3 1 0
  | 6 => tabC55 4 2 3 1 1
  | 7 => tabC55 4 2 3 1 2
  | 8 => tabC55 4 2 3 1 3
  | 9 => tabC55 4 2 3 1 4
  | 10 => tabC55 4 2 3 2 0
  | 11 => tabC55 4 2 3 2 1
  | 12 => tabC55 4 2 3 2 2
  | 13 => tabC55 4 2 3 2 3
  | 14 => tabC55 4 2 3 2 4
  | 15 => tabC55 4 2 3 3 0
  | 16 => tabC55 4 2 3 3 1
  | 17 => tabC55 4 2 3 3 2
  | 18 => tabC55 4 2 3 3 3
  | 19 => tabC55 4 2 3 3 4
  | 20 => tabC55 4 2 3 4 0
  | 21 => tabC55 4 2 3 4 1
  | 22 => tabC55 4 2 3 4 2
  | 23 => tabC55 4 2 3 4 3
  | 24 => tabC55 4 2 3 4 4
  | 25 => tabC55 4 2 4 0 0
  | 26 => tabC55 4 2 4 0 1
  | 27 => tabC55 4 2 4 0 2
  | 28 => tabC55 4 2 4 0 3
  | 29 => tabC55 4 2 4 0 4
  | 30 => tabC55 4 2 4 1 0
  | 31 => tabC55 4 2 4 1 1
  | 32 => tabC55 4 2 4 1 2
  | 33 => tabC55 4 2 4 1 3
  | 34 => tabC55 4 2 4 1 4
  | 35 => tabC55 4 2 4 2 0
  | 36 => tabC55 4 2 4 2 1
  | 37 => tabC55 4 2 4 2 2
  | 38 => tabC55 4 2 4 2 3
  | 39 => tabC55 4 2 4 2 4
  | 40 => tabC55 4 2 4 3 0
  | 41 => tabC55 4 2 4 3 1
  | 42 => tabC55 4 2 4 3 2
  | 43 => tabC55 4 2 4 3 3
  | 44 => tabC55 4 2 4 3 4
  | 45 => tabC55 4 2 4 4 0
  | 46 => tabC55 4 2 4 4 1
  | 47 => tabC55 4 2 4 4 2
  | 48 => tabC55 4 2 4 4 3
  | 49 => tabC55 4 2 4 4 4
  | 50 => tabC55 4 3 0 0 0
  | 51 => tabC55 4 3 0 0 1
  | 52 => tabC55 4 3 0 0 2
  | 53 => tabC55 4 3 0 0 3
  | 54 => tabC55 4 3 0 0 4
  | _ => tabC55 4 3 0 1 0
def memRowC5551 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 3 0 1 1
  | 1 => tabC55 4 3 0 1 2
  | 2 => tabC55 4 3 0 1 3
  | 3 => tabC55 4 3 0 1 4
  | 4 => tabC55 4 3 0 2 0
  | 5 => tabC55 4 3 0 2 1
  | 6 => tabC55 4 3 0 2 2
  | 7 => tabC55 4 3 0 2 3
  | 8 => tabC55 4 3 0 2 4
  | 9 => tabC55 4 3 0 3 0
  | 10 => tabC55 4 3 0 3 1
  | 11 => tabC55 4 3 0 3 2
  | 12 => tabC55 4 3 0 3 3
  | 13 => tabC55 4 3 0 3 4
  | 14 => tabC55 4 3 0 4 0
  | 15 => tabC55 4 3 0 4 1
  | 16 => tabC55 4 3 0 4 2
  | 17 => tabC55 4 3 0 4 3
  | 18 => tabC55 4 3 0 4 4
  | 19 => tabC55 4 3 1 0 0
  | 20 => tabC55 4 3 1 0 1
  | 21 => tabC55 4 3 1 0 2
  | 22 => tabC55 4 3 1 0 3
  | 23 => tabC55 4 3 1 0 4
  | 24 => tabC55 4 3 1 1 0
  | 25 => tabC55 4 3 1 1 1
  | 26 => tabC55 4 3 1 1 2
  | 27 => tabC55 4 3 1 1 3
  | 28 => tabC55 4 3 1 1 4
  | 29 => tabC55 4 3 1 2 0
  | 30 => tabC55 4 3 1 2 1
  | 31 => tabC55 4 3 1 2 2
  | 32 => tabC55 4 3 1 2 3
  | 33 => tabC55 4 3 1 2 4
  | 34 => tabC55 4 3 1 3 0
  | 35 => tabC55 4 3 1 3 1
  | 36 => tabC55 4 3 1 3 2
  | 37 => tabC55 4 3 1 3 3
  | 38 => tabC55 4 3 1 3 4
  | 39 => tabC55 4 3 1 4 0
  | 40 => tabC55 4 3 1 4 1
  | 41 => tabC55 4 3 1 4 2
  | 42 => tabC55 4 3 1 4 3
  | 43 => tabC55 4 3 1 4 4
  | 44 => tabC55 4 3 2 0 0
  | 45 => tabC55 4 3 2 0 1
  | 46 => tabC55 4 3 2 0 2
  | 47 => tabC55 4 3 2 0 3
  | 48 => tabC55 4 3 2 0 4
  | 49 => tabC55 4 3 2 1 0
  | 50 => tabC55 4 3 2 1 1
  | 51 => tabC55 4 3 2 1 2
  | 52 => tabC55 4 3 2 1 3
  | 53 => tabC55 4 3 2 1 4
  | 54 => tabC55 4 3 2 2 0
  | _ => tabC55 4 3 2 2 1
def memRowC5552 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 3 2 2 2
  | 1 => tabC55 4 3 2 2 3
  | 2 => tabC55 4 3 2 2 4
  | 3 => tabC55 4 3 2 3 0
  | 4 => tabC55 4 3 2 3 1
  | 5 => tabC55 4 3 2 3 2
  | 6 => tabC55 4 3 2 3 3
  | 7 => tabC55 4 3 2 3 4
  | 8 => tabC55 4 3 2 4 0
  | 9 => tabC55 4 3 2 4 1
  | 10 => tabC55 4 3 2 4 2
  | 11 => tabC55 4 3 2 4 3
  | 12 => tabC55 4 3 2 4 4
  | 13 => tabC55 4 3 3 0 0
  | 14 => tabC55 4 3 3 0 1
  | 15 => tabC55 4 3 3 0 2
  | 16 => tabC55 4 3 3 0 3
  | 17 => tabC55 4 3 3 0 4
  | 18 => tabC55 4 3 3 1 0
  | 19 => tabC55 4 3 3 1 1
  | 20 => tabC55 4 3 3 1 2
  | 21 => tabC55 4 3 3 1 3
  | 22 => tabC55 4 3 3 1 4
  | 23 => tabC55 4 3 3 2 0
  | 24 => tabC55 4 3 3 2 1
  | 25 => tabC55 4 3 3 2 2
  | 26 => tabC55 4 3 3 2 3
  | 27 => tabC55 4 3 3 2 4
  | 28 => tabC55 4 3 3 3 0
  | 29 => tabC55 4 3 3 3 1
  | 30 => tabC55 4 3 3 3 2
  | 31 => tabC55 4 3 3 3 3
  | 32 => tabC55 4 3 3 3 4
  | 33 => tabC55 4 3 3 4 0
  | 34 => tabC55 4 3 3 4 1
  | 35 => tabC55 4 3 3 4 2
  | 36 => tabC55 4 3 3 4 3
  | 37 => tabC55 4 3 3 4 4
  | 38 => tabC55 4 3 4 0 0
  | 39 => tabC55 4 3 4 0 1
  | 40 => tabC55 4 3 4 0 2
  | 41 => tabC55 4 3 4 0 3
  | 42 => tabC55 4 3 4 0 4
  | 43 => tabC55 4 3 4 1 0
  | 44 => tabC55 4 3 4 1 1
  | 45 => tabC55 4 3 4 1 2
  | 46 => tabC55 4 3 4 1 3
  | 47 => tabC55 4 3 4 1 4
  | 48 => tabC55 4 3 4 2 0
  | 49 => tabC55 4 3 4 2 1
  | 50 => tabC55 4 3 4 2 2
  | 51 => tabC55 4 3 4 2 3
  | 52 => tabC55 4 3 4 2 4
  | 53 => tabC55 4 3 4 3 0
  | 54 => tabC55 4 3 4 3 1
  | _ => tabC55 4 3 4 3 2
def memRowC5553 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 3 4 3 3
  | 1 => tabC55 4 3 4 3 4
  | 2 => tabC55 4 3 4 4 0
  | 3 => tabC55 4 3 4 4 1
  | 4 => tabC55 4 3 4 4 2
  | 5 => tabC55 4 3 4 4 3
  | 6 => tabC55 4 3 4 4 4
  | 7 => tabC55 4 4 0 0 0
  | 8 => tabC55 4 4 0 0 1
  | 9 => tabC55 4 4 0 0 2
  | 10 => tabC55 4 4 0 0 3
  | 11 => tabC55 4 4 0 0 4
  | 12 => tabC55 4 4 0 1 0
  | 13 => tabC55 4 4 0 1 1
  | 14 => tabC55 4 4 0 1 2
  | 15 => tabC55 4 4 0 1 3
  | 16 => tabC55 4 4 0 1 4
  | 17 => tabC55 4 4 0 2 0
  | 18 => tabC55 4 4 0 2 1
  | 19 => tabC55 4 4 0 2 2
  | 20 => tabC55 4 4 0 2 3
  | 21 => tabC55 4 4 0 2 4
  | 22 => tabC55 4 4 0 3 0
  | 23 => tabC55 4 4 0 3 1
  | 24 => tabC55 4 4 0 3 2
  | 25 => tabC55 4 4 0 3 3
  | 26 => tabC55 4 4 0 3 4
  | 27 => tabC55 4 4 0 4 0
  | 28 => tabC55 4 4 0 4 1
  | 29 => tabC55 4 4 0 4 2
  | 30 => tabC55 4 4 0 4 3
  | 31 => tabC55 4 4 0 4 4
  | 32 => tabC55 4 4 1 0 0
  | 33 => tabC55 4 4 1 0 1
  | 34 => tabC55 4 4 1 0 2
  | 35 => tabC55 4 4 1 0 3
  | 36 => tabC55 4 4 1 0 4
  | 37 => tabC55 4 4 1 1 0
  | 38 => tabC55 4 4 1 1 1
  | 39 => tabC55 4 4 1 1 2
  | 40 => tabC55 4 4 1 1 3
  | 41 => tabC55 4 4 1 1 4
  | 42 => tabC55 4 4 1 2 0
  | 43 => tabC55 4 4 1 2 1
  | 44 => tabC55 4 4 1 2 2
  | 45 => tabC55 4 4 1 2 3
  | 46 => tabC55 4 4 1 2 4
  | 47 => tabC55 4 4 1 3 0
  | 48 => tabC55 4 4 1 3 1
  | 49 => tabC55 4 4 1 3 2
  | 50 => tabC55 4 4 1 3 3
  | 51 => tabC55 4 4 1 3 4
  | 52 => tabC55 4 4 1 4 0
  | 53 => tabC55 4 4 1 4 1
  | 54 => tabC55 4 4 1 4 2
  | _ => tabC55 4 4 1 4 3
def memRowC5554 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 4 1 4 4
  | 1 => tabC55 4 4 2 0 0
  | 2 => tabC55 4 4 2 0 1
  | 3 => tabC55 4 4 2 0 2
  | 4 => tabC55 4 4 2 0 3
  | 5 => tabC55 4 4 2 0 4
  | 6 => tabC55 4 4 2 1 0
  | 7 => tabC55 4 4 2 1 1
  | 8 => tabC55 4 4 2 1 2
  | 9 => tabC55 4 4 2 1 3
  | 10 => tabC55 4 4 2 1 4
  | 11 => tabC55 4 4 2 2 0
  | 12 => tabC55 4 4 2 2 1
  | 13 => tabC55 4 4 2 2 2
  | 14 => tabC55 4 4 2 2 3
  | 15 => tabC55 4 4 2 2 4
  | 16 => tabC55 4 4 2 3 0
  | 17 => tabC55 4 4 2 3 1
  | 18 => tabC55 4 4 2 3 2
  | 19 => tabC55 4 4 2 3 3
  | 20 => tabC55 4 4 2 3 4
  | 21 => tabC55 4 4 2 4 0
  | 22 => tabC55 4 4 2 4 1
  | 23 => tabC55 4 4 2 4 2
  | 24 => tabC55 4 4 2 4 3
  | 25 => tabC55 4 4 2 4 4
  | 26 => tabC55 4 4 3 0 0
  | 27 => tabC55 4 4 3 0 1
  | 28 => tabC55 4 4 3 0 2
  | 29 => tabC55 4 4 3 0 3
  | 30 => tabC55 4 4 3 0 4
  | 31 => tabC55 4 4 3 1 0
  | 32 => tabC55 4 4 3 1 1
  | 33 => tabC55 4 4 3 1 2
  | 34 => tabC55 4 4 3 1 3
  | 35 => tabC55 4 4 3 1 4
  | 36 => tabC55 4 4 3 2 0
  | 37 => tabC55 4 4 3 2 1
  | 38 => tabC55 4 4 3 2 2
  | 39 => tabC55 4 4 3 2 3
  | 40 => tabC55 4 4 3 2 4
  | 41 => tabC55 4 4 3 3 0
  | 42 => tabC55 4 4 3 3 1
  | 43 => tabC55 4 4 3 3 2
  | 44 => tabC55 4 4 3 3 3
  | 45 => tabC55 4 4 3 3 4
  | 46 => tabC55 4 4 3 4 0
  | 47 => tabC55 4 4 3 4 1
  | 48 => tabC55 4 4 3 4 2
  | 49 => tabC55 4 4 3 4 3
  | 50 => tabC55 4 4 3 4 4
  | 51 => tabC55 4 4 4 0 0
  | 52 => tabC55 4 4 4 0 1
  | 53 => tabC55 4 4 4 0 2
  | 54 => tabC55 4 4 4 0 3
  | _ => tabC55 4 4 4 0 4
def memRowC5555 : Fin 56 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabC55 4 4 4 1 0
  | 1 => tabC55 4 4 4 1 1
  | 2 => tabC55 4 4 4 1 2
  | 3 => tabC55 4 4 4 1 3
  | 4 => tabC55 4 4 4 1 4
  | 5 => tabC55 4 4 4 2 0
  | 6 => tabC55 4 4 4 2 1
  | 7 => tabC55 4 4 4 2 2
  | 8 => tabC55 4 4 4 2 3
  | 9 => tabC55 4 4 4 2 4
  | 10 => tabC55 4 4 4 3 0
  | 11 => tabC55 4 4 4 3 1
  | 12 => tabC55 4 4 4 3 2
  | 13 => tabC55 4 4 4 3 3
  | 14 => tabC55 4 4 4 3 4
  | 15 => tabC55 4 4 4 4 0
  | 16 => tabC55 4 4 4 4 1
  | 17 => tabC55 4 4 4 4 2
  | 18 => tabC55 4 4 4 4 3
  | _ => tabC55 4 4 4 4 4
def memC55 (i : Fin 3100) : Fin 5 → Fin 5 → Fin 5 :=
  match (i.1 / 56 : Nat) with
  | 0 => memRowC550 ⟨i.1 % 56, by omega⟩
  | 1 => memRowC551 ⟨i.1 % 56, by omega⟩
  | 2 => memRowC552 ⟨i.1 % 56, by omega⟩
  | 3 => memRowC553 ⟨i.1 % 56, by omega⟩
  | 4 => memRowC554 ⟨i.1 % 56, by omega⟩
  | 5 => memRowC555 ⟨i.1 % 56, by omega⟩
  | 6 => memRowC556 ⟨i.1 % 56, by omega⟩
  | 7 => memRowC557 ⟨i.1 % 56, by omega⟩
  | 8 => memRowC558 ⟨i.1 % 56, by omega⟩
  | 9 => memRowC559 ⟨i.1 % 56, by omega⟩
  | 10 => memRowC5510 ⟨i.1 % 56, by omega⟩
  | 11 => memRowC5511 ⟨i.1 % 56, by omega⟩
  | 12 => memRowC5512 ⟨i.1 % 56, by omega⟩
  | 13 => memRowC5513 ⟨i.1 % 56, by omega⟩
  | 14 => memRowC5514 ⟨i.1 % 56, by omega⟩
  | 15 => memRowC5515 ⟨i.1 % 56, by omega⟩
  | 16 => memRowC5516 ⟨i.1 % 56, by omega⟩
  | 17 => memRowC5517 ⟨i.1 % 56, by omega⟩
  | 18 => memRowC5518 ⟨i.1 % 56, by omega⟩
  | 19 => memRowC5519 ⟨i.1 % 56, by omega⟩
  | 20 => memRowC5520 ⟨i.1 % 56, by omega⟩
  | 21 => memRowC5521 ⟨i.1 % 56, by omega⟩
  | 22 => memRowC5522 ⟨i.1 % 56, by omega⟩
  | 23 => memRowC5523 ⟨i.1 % 56, by omega⟩
  | 24 => memRowC5524 ⟨i.1 % 56, by omega⟩
  | 25 => memRowC5525 ⟨i.1 % 56, by omega⟩
  | 26 => memRowC5526 ⟨i.1 % 56, by omega⟩
  | 27 => memRowC5527 ⟨i.1 % 56, by omega⟩
  | 28 => memRowC5528 ⟨i.1 % 56, by omega⟩
  | 29 => memRowC5529 ⟨i.1 % 56, by omega⟩
  | 30 => memRowC5530 ⟨i.1 % 56, by omega⟩
  | 31 => memRowC5531 ⟨i.1 % 56, by omega⟩
  | 32 => memRowC5532 ⟨i.1 % 56, by omega⟩
  | 33 => memRowC5533 ⟨i.1 % 56, by omega⟩
  | 34 => memRowC5534 ⟨i.1 % 56, by omega⟩
  | 35 => memRowC5535 ⟨i.1 % 56, by omega⟩
  | 36 => memRowC5536 ⟨i.1 % 56, by omega⟩
  | 37 => memRowC5537 ⟨i.1 % 56, by omega⟩
  | 38 => memRowC5538 ⟨i.1 % 56, by omega⟩
  | 39 => memRowC5539 ⟨i.1 % 56, by omega⟩
  | 40 => memRowC5540 ⟨i.1 % 56, by omega⟩
  | 41 => memRowC5541 ⟨i.1 % 56, by omega⟩
  | 42 => memRowC5542 ⟨i.1 % 56, by omega⟩
  | 43 => memRowC5543 ⟨i.1 % 56, by omega⟩
  | 44 => memRowC5544 ⟨i.1 % 56, by omega⟩
  | 45 => memRowC5545 ⟨i.1 % 56, by omega⟩
  | 46 => memRowC5546 ⟨i.1 % 56, by omega⟩
  | 47 => memRowC5547 ⟨i.1 % 56, by omega⟩
  | 48 => memRowC5548 ⟨i.1 % 56, by omega⟩
  | 49 => memRowC5549 ⟨i.1 % 56, by omega⟩
  | 50 => memRowC5550 ⟨i.1 % 56, by omega⟩
  | 51 => memRowC5551 ⟨i.1 % 56, by omega⟩
  | 52 => memRowC5552 ⟨i.1 % 56, by omega⟩
  | 53 => memRowC5553 ⟨i.1 % 56, by omega⟩
  | 54 => memRowC5554 ⟨i.1 % 56, by omega⟩
  | _ => memRowC5555 ⟨i.1 % 56, by omega⟩

/-- Which of the `3100` members a given invariant tuple is, so that `mem_of_isExactC55` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrC55 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 0, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 51, 0, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
  71, 72, 0, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
  94, 95, 96, 97, 0, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112,
  113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
  132, 133, 134, 0, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
  150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 0, 162, 163, 164, 165, 166, 167,
  168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186,
  0, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
  205, 206, 207, 0, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
  223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 0, 233, 234, 235, 236, 237, 238, 239, 240,
  241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259,
  0, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277,
  278, 279, 280, 281, 282, 283, 284, 285, 286, 0, 287, 288, 289, 290, 291, 292, 293, 294, 295,
  296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 0, 312, 313,
  314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332,
  0, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350,
  351, 352, 353, 354, 355, 356, 357, 0, 358, 359, 360, 361, 362, 363, 364, 0, 365, 366, 367, 368,
  369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387,
  388, 389, 390, 391, 0, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
  406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 0, 417, 418, 419, 420, 421, 422, 423,
  424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 0, 438, 439, 440, 441,
  442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460,
  461, 462, 0, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478,
  479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 0, 490, 491, 492, 493, 494, 495, 496,
  497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515,
  516, 0, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533,
  534, 535, 536, 537, 538, 539, 540, 541, 0, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551,
  552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 0, 563, 564, 565, 566, 567, 568, 569,
  570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 0,
  588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606,
  607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625,
  626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644,
  645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663,
  664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682,
  683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701,
  702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720,
  721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739,
  740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758,
  759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777,
  778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796,
  797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815,
  816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834,
  835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853,
  854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872,
  873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891,
  892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910,
  911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929,
  930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948,
  949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967,
  968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986,
  987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004,
  1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020,
  1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036,
  1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052,
  1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068,
  1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084,
  1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100,
  1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116,
  1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132,
  1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148,
  1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164,
  1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180,
  1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196,
  1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212,
  1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228,
  1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244,
  1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260,
  1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276,
  1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292,
  1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308,
  1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324,
  1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340,
  1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356,
  1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372,
  1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388,
  1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404,
  1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420,
  1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436,
  1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452,
  1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468,
  1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484,
  1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500,
  1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516,
  1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532,
  1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548,
  1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564,
  1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580,
  1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596,
  1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612,
  1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628,
  1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644,
  1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660,
  1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676,
  1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692,
  1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708,
  1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724,
  1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740,
  1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756,
  1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772,
  1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788,
  1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804,
  1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820,
  1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836,
  1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852,
  1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868,
  1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884,
  1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900,
  1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916,
  1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932,
  1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948,
  1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964,
  1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980,
  1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996,
  1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012,
  2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028,
  2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044,
  2045, 2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060,
  2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076,
  2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092,
  2093, 2094, 2095, 2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108,
  2109, 2110, 2111, 2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124,
  2125, 2126, 2127, 2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140,
  2141, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156,
  2157, 2158, 2159, 2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172,
  2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188,
  2189, 2190, 2191, 2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204,
  2205, 2206, 2207, 2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220,
  2221, 2222, 2223, 2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236,
  2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252,
  2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268,
  2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284,
  2285, 2286, 2287, 2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300,
  2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316,
  2317, 2318, 2319, 2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332,
  2333, 2334, 2335, 2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348,
  2349, 2350, 2351, 2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364,
  2365, 2366, 2367, 2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380,
  2381, 2382, 2383, 2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396,
  2397, 2398, 2399, 2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412,
  2413, 2414, 2415, 2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428,
  2429, 2430, 2431, 2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444,
  2445, 2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460,
  2461, 2462, 2463, 2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476,
  2477, 2478, 2479, 2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492,
  2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508,
  2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524,
  2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540,
  2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556,
  2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572,
  2573, 2574, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588,
  2589, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604,
  2605, 2606, 2607, 2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620,
  2621, 2622, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636,
  2637, 2638, 2639, 2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652,
  2653, 2654, 2655, 2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668,
  2669, 2670, 2671, 2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684,
  2685, 2686, 2687, 2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700,
  2701, 2702, 2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716,
  2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732,
  2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748,
  2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764,
  2765, 2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780,
  2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796,
  2797, 2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812,
  2813, 2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828,
  2829, 2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844,
  2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860,
  2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876,
  2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892,
  2893, 2894, 2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908,
  2909, 2910, 2911, 2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924,
  2925, 2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940,
  2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956,
  2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972,
  2973, 2974, 2975, 2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988,
  2989, 2990, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004,
  3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020,
  3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036,
  3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052,
  3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068,
  3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084,
  3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099]

/-- The arguments as one mixed-radix index, which is how `rankArrC55` is addressed. -/
def encTC55 (a b c d e : Fin 5) : Nat :=
  a.1 * 625 +
    b.1 * 125 +
    c.1 * 25 +
    d.1 * 5 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankC55 (a b c d e : Fin 5) : Fin 3100 :=
  ⟨min (rankArrC55.getD (encTC55 a b c d e) 0) 3099, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactC55 (i : Fin 3100) : Magma (Fin 5) := Magma.mk (memC55 i)

theorem exactC55_isEndo (i : Fin 3100) (j : Fin 5) : (exactC55 i).IsEndo ⇑(eEC55 j) := by
  simp only [eEC55, coe_permOf]; revert i j; native_decide

theorem exactC55_not_isEndo (i : Fin 3100) (j : Fin 1) : ¬ (exactC55 i).IsEndo ⇑(eXC55 j) := by
  simp only [eXC55, coe_permOf]; revert i j; native_decide

/-- `rankC55` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memC55` for the index would be a comparison per tuple and
member. -/
theorem mem_rankC55 (a b c d e : Fin 5)
    (h : Magma.isExact (tabC55 a b c d e) permEC55 permXC55 = true) :
    memC55 (rankC55 a b c d e) = tabC55 a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `3100`
listed members. -/
theorem mem_of_isExactC55 (a b c d e : Fin 5)
    (h : Magma.isExact (tabC55 a b c d e) permEC55 permXC55 = true) :
    ∃ i, memC55 i = tabC55 a b c d e :=
  ⟨_, mem_rankC55 a b c d e h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactC55`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactC55` turns that into a member index. -/
theorem exists_exactC55 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eEC55 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXC55 i)) : ∃ i, exactC55 i = M := by
  simp only [eEC55, coe_permOf] at hE
  simp only [eXC55, coe_permOf] at hX
  have hop : M.op = Magma.transport permEC55 trC55 (fun i ↦ M.op (repC55 i).1 (repC55 i).2) :=
    Magma.op_eq_transport (rep := repC55) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEC55) (idx := stabIdxC550) (a := (repC55 0).1) (b := (repC55 0).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEC55) (idx := stabIdxC551) (a := (repC55 1).1) (b := (repC55 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEC55) (idx := stabIdxC552) (a := (repC55 2).1) (b := (repC55 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEC55) (idx := stabIdxC553) (a := (repC55 3).1) (b := (repC55 3).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEC55) (idx := stabIdxC554) (a := (repC55 4).1) (b := (repC55 4).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decC55 a b c d e = fun i ↦ M.op (repC55 i).1 (repC55 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tabC55 a b c d e = M.op := by
    rw [tabC55_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabC55 a b c d e) permEC55 permXC55 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactC55 a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`5` group of `Magma.permEC55`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactC55 {L L' : Law.NatMagmaLaw} {i : Fin 3100}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactC55 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactC55 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactC55 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactC55
    (fun k ↦ (Magma.exactC55_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactC55_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
