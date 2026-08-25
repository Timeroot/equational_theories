import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D147` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`14` group `⟨(0 1 4 5 6 3 2), (1 2)(3 4)(5 6)⟩` -/

/-- The `14` elements of the group: `()`, `(1 2)(3 4)(5 6)`, `(0 1)(2 4)(3 5)`, `(0 1 4 5 6 3 2)`,
`(0 2 3 6 5 4 1)`, `(0 2)(1 3)(4 6)`, `(0 3 5 1 2 6 4)`, `(0 3)(1 6)(4 5)`, `(0 4)(2 5)(3 6)`, `(0 4
6 2 1 5 3)`, `(0 5)(1 4)(2 6)`, `(0 5 2 4 3 1 6)`, `(0 6 1 3 4 2 5)`, `(0 6)(1 5)(2 3)`. -/
def pED1470 : Fin 7 → Fin 7 := id
def pED1471 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pED1472 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 6
def pED1473 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 3
def pED1474 : Fin 7 → Fin 7 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 6 | 4 => 1 | 5 => 4 | 6 => 5
def pED1475 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4
def pED1476 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 6 | 3 => 5 | 4 => 0 | 5 => 1 | 6 => 4
def pED1477 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 1
def pED1478 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 5 | 3 => 6 | 4 => 0 | 5 => 2 | 6 => 3
def pED1479 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 1 | 3 => 0 | 4 => 6 | 5 => 3 | 6 => 2
def pED14710 : Fin 7 → Fin 7 | 0 => 5 | 1 => 4 | 2 => 6 | 3 => 3 | 4 => 1 | 5 => 0 | 6 => 2
def pED14711 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 0
def pED14712 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 0 | 6 => 1
def pED14713 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 1 | 6 => 0

def permED147 : Fin 14 → Fin 7 → Fin 7
  | 0 => pED1470
  | 1 => pED1471
  | 2 => pED1472
  | 3 => pED1473
  | 4 => pED1474
  | 5 => pED1475
  | 6 => pED1476
  | 7 => pED1477
  | 8 => pED1478
  | 9 => pED1479
  | 10 => pED14710
  | 11 => pED14711
  | 12 => pED14712
  | 13 => pED14713

def permEinvD147 : Fin 14 → Fin 7 → Fin 7
  | 0 => pED1470
  | 1 => pED1471
  | 2 => pED1472
  | 3 => pED1474
  | 4 => pED1473
  | 5 => pED1475
  | 6 => pED1479
  | 7 => pED1477
  | 8 => pED1478
  | 9 => pED1476
  | 10 => pED14710
  | 11 => pED14712
  | 12 => pED14711
  | 13 => pED14713

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED147 (i : Fin 14) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permED147 i) (permEinvD147 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3 4 1 5 2)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXD1470 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 2 | 6 => 6
def pXD1470inv : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 3 | 5 => 1 | 6 => 6

def permXD147 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXD1470

def permXinvD147 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXD1470inv

def eXD147 (i : Fin 1) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXD147 i) (permXinvD147 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `4`, so an invariant
operation is `4` values. -/
def repD147 : Fin 4 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD147 : Fin 7 → Fin 7 → Fin 4 × Fin 14
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (2, 1)
  | 0, 5 => (3, 0)
  | 0, 6 => (3, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (2, 3)
  | 1, 3 => (3, 2)
  | 1, 4 => (1, 3)
  | 1, 5 => (2, 2)
  | 1, 6 => (3, 3)
  | 2, 0 => (1, 4)
  | 2, 1 => (2, 5)
  | 2, 2 => (0, 4)
  | 2, 3 => (1, 5)
  | 2, 4 => (3, 4)
  | 2, 5 => (3, 5)
  | 2, 6 => (2, 4)
  | 3, 0 => (2, 7)
  | 3, 1 => (3, 6)
  | 3, 2 => (1, 6)
  | 3, 3 => (0, 6)
  | 3, 4 => (3, 7)
  | 3, 5 => (2, 6)
  | 3, 6 => (1, 7)
  | 4, 0 => (2, 9)
  | 4, 1 => (1, 8)
  | 4, 2 => (3, 8)
  | 4, 3 => (3, 9)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 9)
  | 4, 6 => (2, 8)
  | 5, 0 => (3, 10)
  | 5, 1 => (2, 11)
  | 5, 2 => (3, 11)
  | 5, 3 => (2, 10)
  | 5, 4 => (1, 10)
  | 5, 5 => (0, 10)
  | 5, 6 => (1, 11)
  | 6, 0 => (3, 12)
  | 6, 1 => (3, 13)
  | 6, 2 => (2, 13)
  | 6, 3 => (1, 12)
  | 6, 4 => (2, 12)
  | 6, 5 => (1, 13)
  | 6, 6 => (0, 12)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxD1470 : Fin 2 → Fin 14
  | 0 => 0
  | 1 => 1
def valD1470 : Fin 1 → Fin 7
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxD1471 : Fin 1 → Fin 14
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxD1472 : Fin 1 → Fin 14
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxD1473 : Fin 1 → Fin 14
  | 0 => 0

/-- The `4` orbit values named by the family's arguments. -/
def decD147 (a : Fin 1) (b c d : Fin 7) : Fin 4 → Fin 7
  | 0 => valD1470 a
  | 1 => b
  | 2 => c
  | 3 => d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD147_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD147 (a : Fin 1) (b c d : Fin 7) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valD1470 a
  | 0, 1 => b
  | 0, 2 => pED1471 b
  | 0, 3 => c
  | 0, 4 => pED1471 c
  | 0, 5 => d
  | 0, 6 => pED1471 d
  | 1, 0 => pED1472 b
  | 1, 1 => pED1472 (valD1470 a)
  | 1, 2 => pED1473 c
  | 1, 3 => pED1472 d
  | 1, 4 => pED1473 b
  | 1, 5 => pED1472 c
  | 1, 6 => pED1473 d
  | 2, 0 => pED1474 b
  | 2, 1 => pED1475 c
  | 2, 2 => pED1474 (valD1470 a)
  | 2, 3 => pED1475 b
  | 2, 4 => pED1474 d
  | 2, 5 => pED1475 d
  | 2, 6 => pED1474 c
  | 3, 0 => pED1477 c
  | 3, 1 => pED1476 d
  | 3, 2 => pED1476 b
  | 3, 3 => pED1476 (valD1470 a)
  | 3, 4 => pED1477 d
  | 3, 5 => pED1476 c
  | 3, 6 => pED1477 b
  | 4, 0 => pED1479 c
  | 4, 1 => pED1478 b
  | 4, 2 => pED1478 d
  | 4, 3 => pED1479 d
  | 4, 4 => pED1478 (valD1470 a)
  | 4, 5 => pED1479 b
  | 4, 6 => pED1478 c
  | 5, 0 => pED14710 d
  | 5, 1 => pED14711 c
  | 5, 2 => pED14711 d
  | 5, 3 => pED14710 c
  | 5, 4 => pED14710 b
  | 5, 5 => pED14710 (valD1470 a)
  | 5, 6 => pED14711 b
  | 6, 0 => pED14712 d
  | 6, 1 => pED14713 d
  | 6, 2 => pED14713 c
  | 6, 3 => pED14712 b
  | 6, 4 => pED14712 c
  | 6, 5 => pED14713 b
  | 6, 6 => pED14712 (valD1470 a)

theorem tabD147_eq_transport (a : Fin 1) (b c d : Fin 7) :
    tabD147 a b c d = Magma.transport permED147 trD147 (decD147 a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `336` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `343` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowD1470 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 0 0 1
  | 1 => tabD147 0 0 0 2
  | 2 => tabD147 0 0 0 3
  | 3 => tabD147 0 0 0 4
  | 4 => tabD147 0 0 0 5
  | 5 => tabD147 0 0 0 6
  | 6 => tabD147 0 0 1 0
  | 7 => tabD147 0 0 1 1
  | 8 => tabD147 0 0 1 2
  | 9 => tabD147 0 0 1 3
  | 10 => tabD147 0 0 1 4
  | 11 => tabD147 0 0 1 5
  | 12 => tabD147 0 0 1 6
  | 13 => tabD147 0 0 2 0
  | 14 => tabD147 0 0 2 1
  | 15 => tabD147 0 0 2 2
  | 16 => tabD147 0 0 2 3
  | 17 => tabD147 0 0 2 4
  | _ => tabD147 0 0 2 5
def memRowD1471 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 0 2 6
  | 1 => tabD147 0 0 3 0
  | 2 => tabD147 0 0 3 1
  | 3 => tabD147 0 0 3 2
  | 4 => tabD147 0 0 3 3
  | 5 => tabD147 0 0 3 4
  | 6 => tabD147 0 0 3 5
  | 7 => tabD147 0 0 3 6
  | 8 => tabD147 0 0 4 0
  | 9 => tabD147 0 0 4 1
  | 10 => tabD147 0 0 4 2
  | 11 => tabD147 0 0 4 3
  | 12 => tabD147 0 0 4 4
  | 13 => tabD147 0 0 4 5
  | 14 => tabD147 0 0 4 6
  | 15 => tabD147 0 0 5 0
  | 16 => tabD147 0 0 5 1
  | 17 => tabD147 0 0 5 2
  | _ => tabD147 0 0 5 3
def memRowD1472 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 0 5 4
  | 1 => tabD147 0 0 5 5
  | 2 => tabD147 0 0 5 6
  | 3 => tabD147 0 0 6 0
  | 4 => tabD147 0 0 6 1
  | 5 => tabD147 0 0 6 2
  | 6 => tabD147 0 0 6 3
  | 7 => tabD147 0 0 6 4
  | 8 => tabD147 0 0 6 5
  | 9 => tabD147 0 0 6 6
  | 10 => tabD147 0 1 0 0
  | 11 => tabD147 0 1 0 1
  | 12 => tabD147 0 1 0 2
  | 13 => tabD147 0 1 0 3
  | 14 => tabD147 0 1 0 4
  | 15 => tabD147 0 1 0 5
  | 16 => tabD147 0 1 0 6
  | 17 => tabD147 0 1 1 0
  | _ => tabD147 0 1 1 1
def memRowD1473 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 1 1 2
  | 1 => tabD147 0 1 1 3
  | 2 => tabD147 0 1 1 4
  | 3 => tabD147 0 1 1 5
  | 4 => tabD147 0 1 1 6
  | 5 => tabD147 0 1 2 0
  | 6 => tabD147 0 1 2 1
  | 7 => tabD147 0 1 2 2
  | 8 => tabD147 0 1 2 3
  | 9 => tabD147 0 1 2 4
  | 10 => tabD147 0 1 2 5
  | 11 => tabD147 0 1 2 6
  | 12 => tabD147 0 1 3 0
  | 13 => tabD147 0 1 3 1
  | 14 => tabD147 0 1 3 2
  | 15 => tabD147 0 1 3 3
  | 16 => tabD147 0 1 3 4
  | 17 => tabD147 0 1 3 6
  | _ => tabD147 0 1 4 0
def memRowD1474 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 1 4 1
  | 1 => tabD147 0 1 4 2
  | 2 => tabD147 0 1 4 3
  | 3 => tabD147 0 1 4 4
  | 4 => tabD147 0 1 4 5
  | 5 => tabD147 0 1 4 6
  | 6 => tabD147 0 1 5 0
  | 7 => tabD147 0 1 5 1
  | 8 => tabD147 0 1 5 2
  | 9 => tabD147 0 1 5 3
  | 10 => tabD147 0 1 5 4
  | 11 => tabD147 0 1 5 5
  | 12 => tabD147 0 1 5 6
  | 13 => tabD147 0 1 6 0
  | 14 => tabD147 0 1 6 1
  | 15 => tabD147 0 1 6 2
  | 16 => tabD147 0 1 6 3
  | 17 => tabD147 0 1 6 4
  | _ => tabD147 0 1 6 5
def memRowD1475 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 1 6 6
  | 1 => tabD147 0 2 0 0
  | 2 => tabD147 0 2 0 1
  | 3 => tabD147 0 2 0 2
  | 4 => tabD147 0 2 0 3
  | 5 => tabD147 0 2 0 4
  | 6 => tabD147 0 2 0 5
  | 7 => tabD147 0 2 0 6
  | 8 => tabD147 0 2 1 0
  | 9 => tabD147 0 2 1 1
  | 10 => tabD147 0 2 1 2
  | 11 => tabD147 0 2 1 3
  | 12 => tabD147 0 2 1 4
  | 13 => tabD147 0 2 1 5
  | 14 => tabD147 0 2 1 6
  | 15 => tabD147 0 2 2 0
  | 16 => tabD147 0 2 2 1
  | 17 => tabD147 0 2 2 2
  | _ => tabD147 0 2 2 3
def memRowD1476 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 2 2 4
  | 1 => tabD147 0 2 2 5
  | 2 => tabD147 0 2 2 6
  | 3 => tabD147 0 2 3 0
  | 4 => tabD147 0 2 3 1
  | 5 => tabD147 0 2 3 2
  | 6 => tabD147 0 2 3 3
  | 7 => tabD147 0 2 3 4
  | 8 => tabD147 0 2 3 5
  | 9 => tabD147 0 2 3 6
  | 10 => tabD147 0 2 4 0
  | 11 => tabD147 0 2 4 1
  | 12 => tabD147 0 2 4 2
  | 13 => tabD147 0 2 4 3
  | 14 => tabD147 0 2 4 4
  | 15 => tabD147 0 2 4 5
  | 16 => tabD147 0 2 5 0
  | 17 => tabD147 0 2 5 1
  | _ => tabD147 0 2 5 2
def memRowD1477 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 2 5 3
  | 1 => tabD147 0 2 5 4
  | 2 => tabD147 0 2 5 5
  | 3 => tabD147 0 2 5 6
  | 4 => tabD147 0 2 6 0
  | 5 => tabD147 0 2 6 1
  | 6 => tabD147 0 2 6 2
  | 7 => tabD147 0 2 6 3
  | 8 => tabD147 0 2 6 4
  | 9 => tabD147 0 2 6 5
  | 10 => tabD147 0 2 6 6
  | 11 => tabD147 0 3 0 0
  | 12 => tabD147 0 3 0 1
  | 13 => tabD147 0 3 0 2
  | 14 => tabD147 0 3 0 3
  | 15 => tabD147 0 3 0 4
  | 16 => tabD147 0 3 0 5
  | 17 => tabD147 0 3 0 6
  | _ => tabD147 0 3 1 0
def memRowD1478 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 3 1 1
  | 1 => tabD147 0 3 1 2
  | 2 => tabD147 0 3 1 3
  | 3 => tabD147 0 3 1 4
  | 4 => tabD147 0 3 1 5
  | 5 => tabD147 0 3 1 6
  | 6 => tabD147 0 3 2 0
  | 7 => tabD147 0 3 2 1
  | 8 => tabD147 0 3 2 2
  | 9 => tabD147 0 3 2 3
  | 10 => tabD147 0 3 2 4
  | 11 => tabD147 0 3 2 5
  | 12 => tabD147 0 3 2 6
  | 13 => tabD147 0 3 3 0
  | 14 => tabD147 0 3 3 1
  | 15 => tabD147 0 3 3 2
  | 16 => tabD147 0 3 3 3
  | 17 => tabD147 0 3 3 4
  | _ => tabD147 0 3 3 5
def memRowD1479 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 3 3 6
  | 1 => tabD147 0 3 4 0
  | 2 => tabD147 0 3 4 1
  | 3 => tabD147 0 3 4 2
  | 4 => tabD147 0 3 4 3
  | 5 => tabD147 0 3 4 4
  | 6 => tabD147 0 3 4 5
  | 7 => tabD147 0 3 4 6
  | 8 => tabD147 0 3 5 0
  | 9 => tabD147 0 3 5 1
  | 10 => tabD147 0 3 5 2
  | 11 => tabD147 0 3 5 3
  | 12 => tabD147 0 3 5 4
  | 13 => tabD147 0 3 5 5
  | 14 => tabD147 0 3 5 6
  | 15 => tabD147 0 3 6 0
  | 16 => tabD147 0 3 6 2
  | 17 => tabD147 0 3 6 3
  | _ => tabD147 0 3 6 4
def memRowD14710 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 3 6 5
  | 1 => tabD147 0 3 6 6
  | 2 => tabD147 0 4 0 0
  | 3 => tabD147 0 4 0 1
  | 4 => tabD147 0 4 0 2
  | 5 => tabD147 0 4 0 3
  | 6 => tabD147 0 4 0 4
  | 7 => tabD147 0 4 0 5
  | 8 => tabD147 0 4 0 6
  | 9 => tabD147 0 4 1 0
  | 10 => tabD147 0 4 1 1
  | 11 => tabD147 0 4 1 2
  | 12 => tabD147 0 4 1 3
  | 13 => tabD147 0 4 1 4
  | 14 => tabD147 0 4 1 5
  | 15 => tabD147 0 4 1 6
  | 16 => tabD147 0 4 2 0
  | 17 => tabD147 0 4 2 1
  | _ => tabD147 0 4 2 2
def memRowD14711 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 4 2 3
  | 1 => tabD147 0 4 2 4
  | 2 => tabD147 0 4 2 5
  | 3 => tabD147 0 4 2 6
  | 4 => tabD147 0 4 3 0
  | 5 => tabD147 0 4 3 1
  | 6 => tabD147 0 4 3 2
  | 7 => tabD147 0 4 3 3
  | 8 => tabD147 0 4 3 4
  | 9 => tabD147 0 4 3 5
  | 10 => tabD147 0 4 3 6
  | 11 => tabD147 0 4 4 0
  | 12 => tabD147 0 4 4 1
  | 13 => tabD147 0 4 4 2
  | 14 => tabD147 0 4 4 3
  | 15 => tabD147 0 4 4 4
  | 16 => tabD147 0 4 4 5
  | 17 => tabD147 0 4 4 6
  | _ => tabD147 0 4 5 0
def memRowD14712 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 4 5 1
  | 1 => tabD147 0 4 5 3
  | 2 => tabD147 0 4 5 4
  | 3 => tabD147 0 4 5 5
  | 4 => tabD147 0 4 5 6
  | 5 => tabD147 0 4 6 0
  | 6 => tabD147 0 4 6 1
  | 7 => tabD147 0 4 6 2
  | 8 => tabD147 0 4 6 3
  | 9 => tabD147 0 4 6 4
  | 10 => tabD147 0 4 6 5
  | 11 => tabD147 0 4 6 6
  | 12 => tabD147 0 5 0 0
  | 13 => tabD147 0 5 0 1
  | 14 => tabD147 0 5 0 2
  | 15 => tabD147 0 5 0 3
  | 16 => tabD147 0 5 0 4
  | 17 => tabD147 0 5 0 5
  | _ => tabD147 0 5 0 6
def memRowD14713 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 5 1 0
  | 1 => tabD147 0 5 1 1
  | 2 => tabD147 0 5 1 2
  | 3 => tabD147 0 5 1 3
  | 4 => tabD147 0 5 1 5
  | 5 => tabD147 0 5 1 6
  | 6 => tabD147 0 5 2 0
  | 7 => tabD147 0 5 2 1
  | 8 => tabD147 0 5 2 2
  | 9 => tabD147 0 5 2 3
  | 10 => tabD147 0 5 2 4
  | 11 => tabD147 0 5 2 5
  | 12 => tabD147 0 5 2 6
  | 13 => tabD147 0 5 3 0
  | 14 => tabD147 0 5 3 1
  | 15 => tabD147 0 5 3 2
  | 16 => tabD147 0 5 3 3
  | 17 => tabD147 0 5 3 4
  | _ => tabD147 0 5 3 5
def memRowD14714 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 5 3 6
  | 1 => tabD147 0 5 4 0
  | 2 => tabD147 0 5 4 1
  | 3 => tabD147 0 5 4 2
  | 4 => tabD147 0 5 4 3
  | 5 => tabD147 0 5 4 4
  | 6 => tabD147 0 5 4 5
  | 7 => tabD147 0 5 4 6
  | 8 => tabD147 0 5 5 0
  | 9 => tabD147 0 5 5 1
  | 10 => tabD147 0 5 5 2
  | 11 => tabD147 0 5 5 3
  | 12 => tabD147 0 5 5 4
  | 13 => tabD147 0 5 5 5
  | 14 => tabD147 0 5 5 6
  | 15 => tabD147 0 5 6 0
  | 16 => tabD147 0 5 6 1
  | 17 => tabD147 0 5 6 2
  | _ => tabD147 0 5 6 3
def memRowD14715 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 5 6 4
  | 1 => tabD147 0 5 6 5
  | 2 => tabD147 0 5 6 6
  | 3 => tabD147 0 6 0 0
  | 4 => tabD147 0 6 0 1
  | 5 => tabD147 0 6 0 2
  | 6 => tabD147 0 6 0 3
  | 7 => tabD147 0 6 0 4
  | 8 => tabD147 0 6 0 5
  | 9 => tabD147 0 6 0 6
  | 10 => tabD147 0 6 1 0
  | 11 => tabD147 0 6 1 1
  | 12 => tabD147 0 6 1 2
  | 13 => tabD147 0 6 1 3
  | 14 => tabD147 0 6 1 4
  | 15 => tabD147 0 6 1 5
  | 16 => tabD147 0 6 1 6
  | 17 => tabD147 0 6 2 0
  | _ => tabD147 0 6 2 1
def memRowD14716 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 6 2 2
  | 1 => tabD147 0 6 2 4
  | 2 => tabD147 0 6 2 5
  | 3 => tabD147 0 6 2 6
  | 4 => tabD147 0 6 3 0
  | 5 => tabD147 0 6 3 1
  | 6 => tabD147 0 6 3 2
  | 7 => tabD147 0 6 3 3
  | 8 => tabD147 0 6 3 4
  | 9 => tabD147 0 6 3 5
  | 10 => tabD147 0 6 3 6
  | 11 => tabD147 0 6 4 0
  | 12 => tabD147 0 6 4 1
  | 13 => tabD147 0 6 4 2
  | 14 => tabD147 0 6 4 3
  | 15 => tabD147 0 6 4 4
  | 16 => tabD147 0 6 4 5
  | 17 => tabD147 0 6 4 6
  | _ => tabD147 0 6 5 0
def memRowD14717 : Fin 19 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabD147 0 6 5 1
  | 1 => tabD147 0 6 5 2
  | 2 => tabD147 0 6 5 3
  | 3 => tabD147 0 6 5 4
  | 4 => tabD147 0 6 5 5
  | 5 => tabD147 0 6 5 6
  | 6 => tabD147 0 6 6 0
  | 7 => tabD147 0 6 6 1
  | 8 => tabD147 0 6 6 2
  | 9 => tabD147 0 6 6 3
  | 10 => tabD147 0 6 6 4
  | 11 => tabD147 0 6 6 5
  | _ => tabD147 0 6 6 6
def memD147 (i : Fin 336) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 19 : Nat) with
  | 0 => memRowD1470 ⟨i.1 % 19, by omega⟩
  | 1 => memRowD1471 ⟨i.1 % 19, by omega⟩
  | 2 => memRowD1472 ⟨i.1 % 19, by omega⟩
  | 3 => memRowD1473 ⟨i.1 % 19, by omega⟩
  | 4 => memRowD1474 ⟨i.1 % 19, by omega⟩
  | 5 => memRowD1475 ⟨i.1 % 19, by omega⟩
  | 6 => memRowD1476 ⟨i.1 % 19, by omega⟩
  | 7 => memRowD1477 ⟨i.1 % 19, by omega⟩
  | 8 => memRowD1478 ⟨i.1 % 19, by omega⟩
  | 9 => memRowD1479 ⟨i.1 % 19, by omega⟩
  | 10 => memRowD14710 ⟨i.1 % 19, by omega⟩
  | 11 => memRowD14711 ⟨i.1 % 19, by omega⟩
  | 12 => memRowD14712 ⟨i.1 % 19, by omega⟩
  | 13 => memRowD14713 ⟨i.1 % 19, by omega⟩
  | 14 => memRowD14714 ⟨i.1 % 19, by omega⟩
  | 15 => memRowD14715 ⟨i.1 % 19, by omega⟩
  | 16 => memRowD14716 ⟨i.1 % 19, by omega⟩
  | _ => memRowD14717 ⟨i.1 % 19, by omega⟩

/-- Which of the `336` members a given invariant tuple is, so that `mem_of_isExactD147` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD147 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
  49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72,
  73, 0, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
  96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
  116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 0, 130, 131, 132, 133,
  134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152,
  153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171,
  172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 0, 187, 188, 189,
  190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208,
  209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227,
  228, 0, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245,
  246, 247, 248, 249, 250, 0, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263,
  264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282,
  283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301,
  302, 303, 304, 0, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319,
  320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]

/-- The arguments as one mixed-radix index, which is how `rankArrD147` is addressed. -/
def encTD147 (a : Fin 1) (b c d : Fin 7) : Nat :=
  a.1 * 343 +
    b.1 * 49 +
    c.1 * 7 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD147 (a : Fin 1) (b c d : Fin 7) : Fin 336 :=
  ⟨min (rankArrD147.getD (encTD147 a b c d) 0) 335, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD147 (i : Fin 336) : Magma (Fin 7) := Magma.mk (memD147 i)

theorem exactD147_isEndo (i : Fin 336) (j : Fin 14) : (exactD147 i).IsEndo ⇑(eED147 j) := by
  simp only [eED147, coe_permOf]; revert i j; native_decide

theorem exactD147_not_isEndo (i : Fin 336) (j : Fin 1) : ¬ (exactD147 i).IsEndo ⇑(eXD147 j) := by
  simp only [eXD147, coe_permOf]; revert i j; native_decide

/-- `rankD147` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD147` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD147 (a : Fin 1) (b c d : Fin 7)
    (h : Magma.isExact (tabD147 a b c d) permED147 permXD147 = true) :
    memD147 (rankD147 a b c d) = tabD147 a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `336`
listed members. -/
theorem mem_of_isExactD147 (a : Fin 1) (b c d : Fin 7)
    (h : Magma.isExact (tabD147 a b c d) permED147 permXD147 = true) :
    ∃ i, memD147 i = tabD147 a b c d :=
  ⟨_, mem_rankD147 a b c d h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD147`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD147` turns that into a member index. -/
theorem exists_exactD147 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eED147 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD147 i)) : ∃ i, exactD147 i = M := by
  simp only [eED147, coe_permOf] at hE
  simp only [eXD147, coe_permOf] at hX
  have hop : M.op = Magma.transport permED147 trD147 (fun i ↦ M.op (repD147 i).1 (repD147 i).2) :=
    Magma.op_eq_transport (rep := repD147) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED147) (idx := stabIdxD1470) (a := (repD147 0).1) (b := (repD147 0).2)
    (val := valD1470) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED147) (idx := stabIdxD1471) (a := (repD147 1).1) (b := (repD147 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED147) (idx := stabIdxD1472) (a := (repD147 2).1) (b := (repD147 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permED147) (idx := stabIdxD1473) (a := (repD147 3).1) (b := (repD147 3).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decD147 a b c d = fun i ↦ M.op (repD147 i).1 (repD147 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tabD147 a b c d = M.op := by
    rw [tabD147_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD147 a b c d) permED147 permXD147 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD147 a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`14` group of `Magma.permED147`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD147 {L L' : Law.NatMagmaLaw} {i : Fin 336}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactD147 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactD147 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD147 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD147
    (fun k ↦ (Magma.exactD147_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD147_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
