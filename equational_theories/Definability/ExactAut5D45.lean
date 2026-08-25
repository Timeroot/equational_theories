import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D45` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`8` group `⟨(1 2)(3 4), (1 3)(2 4), (1 3 2 4)⟩` -/

/-- The `8` elements of the group: `()`, `(3 4)`, `(1 2)`, `(1 2)(3 4)`, `(1 3)(2 4)`, `(1 3 2 4)`,
`(1 4 2 3)`, `(1 4)(2 3)`. -/
def pED450 : Fin 5 → Fin 5 := id
def pED451 : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3
def pED452 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4
def pED453 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3
def pED454 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2
def pED455 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1
def pED456 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2
def pED457 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1

def permED45 : Fin 8 → Fin 5 → Fin 5
  | 0 => pED450
  | 1 => pED451
  | 2 => pED452
  | 3 => pED453
  | 4 => pED454
  | 5 => pED455
  | 6 => pED456
  | 7 => pED457

def permEinvD45 : Fin 8 → Fin 5 → Fin 5
  | 0 => pED450
  | 1 => pED451
  | 2 => pED452
  | 3 => pED453
  | 4 => pED454
  | 5 => pED456
  | 6 => pED455
  | 7 => pED457

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED45 (i : Fin 8) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permED45 i) (permEinvD45 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(2 3)`. Every subgroup properly containing
the group above contains it, so a magma admitting the group and not this has that group as its
automorphism group exactly. -/
def pXD450 : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4
def pXD450inv : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4

def permXD45 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXD450

def permXinvD45 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXD450inv

def eXD45 (i : Fin 1) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXD45 i) (permXinvD45 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `6`, so an invariant
operation is `6` values. -/
def repD45 : Fin 6 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)
  | 5 => (1, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD45 : Fin 5 → Fin 5 → Fin 6 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 2)
  | 0, 3 => (1, 4)
  | 0, 4 => (1, 6)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (5, 0)
  | 1, 4 => (5, 1)
  | 2, 0 => (2, 2)
  | 2, 1 => (4, 2)
  | 2, 2 => (3, 2)
  | 2, 3 => (5, 2)
  | 2, 4 => (5, 3)
  | 3, 0 => (2, 4)
  | 3, 1 => (5, 4)
  | 3, 2 => (5, 5)
  | 3, 3 => (3, 4)
  | 3, 4 => (4, 4)
  | 4, 0 => (2, 6)
  | 4, 1 => (5, 6)
  | 4, 2 => (5, 7)
  | 4, 3 => (4, 6)
  | 4, 4 => (3, 6)

/-- The `8` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxD450 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def valD450 : Fin 1 → Fin 5
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD451 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def valD451 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD452 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def valD452 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD453 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def valD453 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD454 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def valD454 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxD455 : Fin 1 → Fin 8
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def decD45 (a : Fin 1) (b c d e : Fin 3) (f : Fin 5) : Fin 6 → Fin 5
  | 0 => valD450 a
  | 1 => valD451 b
  | 2 => valD452 c
  | 3 => valD453 d
  | 4 => valD454 e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD45_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD45 (a : Fin 1) (b c d e : Fin 3) (f : Fin 5) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valD450 a
  | 0, 1 => valD451 b
  | 0, 2 => pED452 (valD451 b)
  | 0, 3 => pED454 (valD451 b)
  | 0, 4 => pED456 (valD451 b)
  | 1, 0 => valD452 c
  | 1, 1 => valD453 d
  | 1, 2 => valD454 e
  | 1, 3 => f
  | 1, 4 => pED451 f
  | 2, 0 => pED452 (valD452 c)
  | 2, 1 => pED452 (valD454 e)
  | 2, 2 => pED452 (valD453 d)
  | 2, 3 => pED452 f
  | 2, 4 => pED453 f
  | 3, 0 => pED454 (valD452 c)
  | 3, 1 => pED454 f
  | 3, 2 => pED455 f
  | 3, 3 => pED454 (valD453 d)
  | 3, 4 => pED454 (valD454 e)
  | 4, 0 => pED456 (valD452 c)
  | 4, 1 => pED456 f
  | 4, 2 => pED457 f
  | 4, 3 => pED456 (valD454 e)
  | 4, 4 => pED456 (valD453 d)

theorem tabD45_eq_transport (a : Fin 1) (b c d e : Fin 3) (f : Fin 5) :
    tabD45 a b c d e f = Magma.transport permED45 trD45 (decD45 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `381` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `405` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowD450 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 0 0 0 1
  | 1 => tabD45 0 0 0 0 0 2
  | 2 => tabD45 0 0 0 0 0 3
  | 3 => tabD45 0 0 0 0 0 4
  | 4 => tabD45 0 0 0 0 1 0
  | 5 => tabD45 0 0 0 0 1 2
  | 6 => tabD45 0 0 0 0 1 3
  | 7 => tabD45 0 0 0 0 1 4
  | 8 => tabD45 0 0 0 0 2 0
  | 9 => tabD45 0 0 0 0 2 1
  | 10 => tabD45 0 0 0 0 2 2
  | 11 => tabD45 0 0 0 0 2 4
  | 12 => tabD45 0 0 0 1 0 1
  | 13 => tabD45 0 0 0 1 0 2
  | 14 => tabD45 0 0 0 1 0 3
  | 15 => tabD45 0 0 0 1 0 4
  | 16 => tabD45 0 0 0 1 1 0
  | 17 => tabD45 0 0 0 1 1 2
  | 18 => tabD45 0 0 0 1 1 3
  | _ => tabD45 0 0 0 1 1 4
def memRowD451 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 0 1 2 0
  | 1 => tabD45 0 0 0 1 2 1
  | 2 => tabD45 0 0 0 1 2 2
  | 3 => tabD45 0 0 0 1 2 4
  | 4 => tabD45 0 0 0 2 0 0
  | 5 => tabD45 0 0 0 2 0 1
  | 6 => tabD45 0 0 0 2 0 2
  | 7 => tabD45 0 0 0 2 0 3
  | 8 => tabD45 0 0 0 2 0 4
  | 9 => tabD45 0 0 0 2 1 0
  | 10 => tabD45 0 0 0 2 1 1
  | 11 => tabD45 0 0 0 2 1 2
  | 12 => tabD45 0 0 0 2 1 3
  | 13 => tabD45 0 0 0 2 1 4
  | 14 => tabD45 0 0 0 2 2 0
  | 15 => tabD45 0 0 0 2 2 1
  | 16 => tabD45 0 0 0 2 2 2
  | 17 => tabD45 0 0 0 2 2 3
  | 18 => tabD45 0 0 0 2 2 4
  | _ => tabD45 0 0 1 0 0 1
def memRowD452 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 1 0 0 2
  | 1 => tabD45 0 0 1 0 0 3
  | 2 => tabD45 0 0 1 0 0 4
  | 3 => tabD45 0 0 1 0 1 0
  | 4 => tabD45 0 0 1 0 1 2
  | 5 => tabD45 0 0 1 0 1 3
  | 6 => tabD45 0 0 1 0 1 4
  | 7 => tabD45 0 0 1 0 2 0
  | 8 => tabD45 0 0 1 0 2 1
  | 9 => tabD45 0 0 1 0 2 2
  | 10 => tabD45 0 0 1 0 2 4
  | 11 => tabD45 0 0 1 1 0 1
  | 12 => tabD45 0 0 1 1 0 2
  | 13 => tabD45 0 0 1 1 0 3
  | 14 => tabD45 0 0 1 1 0 4
  | 15 => tabD45 0 0 1 1 1 0
  | 16 => tabD45 0 0 1 1 1 2
  | 17 => tabD45 0 0 1 1 1 3
  | 18 => tabD45 0 0 1 1 1 4
  | _ => tabD45 0 0 1 1 2 0
def memRowD453 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 1 1 2 1
  | 1 => tabD45 0 0 1 1 2 2
  | 2 => tabD45 0 0 1 1 2 4
  | 3 => tabD45 0 0 1 2 0 0
  | 4 => tabD45 0 0 1 2 0 1
  | 5 => tabD45 0 0 1 2 0 2
  | 6 => tabD45 0 0 1 2 0 3
  | 7 => tabD45 0 0 1 2 0 4
  | 8 => tabD45 0 0 1 2 1 0
  | 9 => tabD45 0 0 1 2 1 1
  | 10 => tabD45 0 0 1 2 1 2
  | 11 => tabD45 0 0 1 2 1 3
  | 12 => tabD45 0 0 1 2 1 4
  | 13 => tabD45 0 0 1 2 2 0
  | 14 => tabD45 0 0 1 2 2 1
  | 15 => tabD45 0 0 1 2 2 2
  | 16 => tabD45 0 0 1 2 2 3
  | 17 => tabD45 0 0 1 2 2 4
  | 18 => tabD45 0 0 2 0 0 0
  | _ => tabD45 0 0 2 0 0 1
def memRowD454 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 2 0 0 2
  | 1 => tabD45 0 0 2 0 0 3
  | 2 => tabD45 0 0 2 0 0 4
  | 3 => tabD45 0 0 2 0 1 0
  | 4 => tabD45 0 0 2 0 1 1
  | 5 => tabD45 0 0 2 0 1 2
  | 6 => tabD45 0 0 2 0 1 3
  | 7 => tabD45 0 0 2 0 1 4
  | 8 => tabD45 0 0 2 0 2 0
  | 9 => tabD45 0 0 2 0 2 1
  | 10 => tabD45 0 0 2 0 2 2
  | 11 => tabD45 0 0 2 0 2 3
  | 12 => tabD45 0 0 2 0 2 4
  | 13 => tabD45 0 0 2 1 0 0
  | 14 => tabD45 0 0 2 1 0 1
  | 15 => tabD45 0 0 2 1 0 2
  | 16 => tabD45 0 0 2 1 0 3
  | 17 => tabD45 0 0 2 1 0 4
  | 18 => tabD45 0 0 2 1 1 0
  | _ => tabD45 0 0 2 1 1 1
def memRowD455 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 2 1 1 2
  | 1 => tabD45 0 0 2 1 1 3
  | 2 => tabD45 0 0 2 1 1 4
  | 3 => tabD45 0 0 2 1 2 0
  | 4 => tabD45 0 0 2 1 2 1
  | 5 => tabD45 0 0 2 1 2 2
  | 6 => tabD45 0 0 2 1 2 3
  | 7 => tabD45 0 0 2 1 2 4
  | 8 => tabD45 0 0 2 2 0 0
  | 9 => tabD45 0 0 2 2 0 1
  | 10 => tabD45 0 0 2 2 0 2
  | 11 => tabD45 0 0 2 2 0 3
  | 12 => tabD45 0 0 2 2 0 4
  | 13 => tabD45 0 0 2 2 1 0
  | 14 => tabD45 0 0 2 2 1 1
  | 15 => tabD45 0 0 2 2 1 2
  | 16 => tabD45 0 0 2 2 1 3
  | 17 => tabD45 0 0 2 2 1 4
  | 18 => tabD45 0 0 2 2 2 0
  | _ => tabD45 0 0 2 2 2 1
def memRowD456 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 0 2 2 2 2
  | 1 => tabD45 0 0 2 2 2 3
  | 2 => tabD45 0 0 2 2 2 4
  | 3 => tabD45 0 1 0 0 0 1
  | 4 => tabD45 0 1 0 0 0 2
  | 5 => tabD45 0 1 0 0 0 3
  | 6 => tabD45 0 1 0 0 0 4
  | 7 => tabD45 0 1 0 0 1 0
  | 8 => tabD45 0 1 0 0 1 2
  | 9 => tabD45 0 1 0 0 1 3
  | 10 => tabD45 0 1 0 0 1 4
  | 11 => tabD45 0 1 0 0 2 0
  | 12 => tabD45 0 1 0 0 2 1
  | 13 => tabD45 0 1 0 0 2 2
  | 14 => tabD45 0 1 0 0 2 4
  | 15 => tabD45 0 1 0 1 0 1
  | 16 => tabD45 0 1 0 1 0 2
  | 17 => tabD45 0 1 0 1 0 3
  | 18 => tabD45 0 1 0 1 0 4
  | _ => tabD45 0 1 0 1 1 0
def memRowD457 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 1 0 1 1 2
  | 1 => tabD45 0 1 0 1 1 3
  | 2 => tabD45 0 1 0 1 1 4
  | 3 => tabD45 0 1 0 1 2 0
  | 4 => tabD45 0 1 0 1 2 1
  | 5 => tabD45 0 1 0 1 2 2
  | 6 => tabD45 0 1 0 1 2 4
  | 7 => tabD45 0 1 0 2 0 0
  | 8 => tabD45 0 1 0 2 0 1
  | 9 => tabD45 0 1 0 2 0 2
  | 10 => tabD45 0 1 0 2 0 3
  | 11 => tabD45 0 1 0 2 0 4
  | 12 => tabD45 0 1 0 2 1 0
  | 13 => tabD45 0 1 0 2 1 1
  | 14 => tabD45 0 1 0 2 1 2
  | 15 => tabD45 0 1 0 2 1 3
  | 16 => tabD45 0 1 0 2 1 4
  | 17 => tabD45 0 1 0 2 2 0
  | 18 => tabD45 0 1 0 2 2 1
  | _ => tabD45 0 1 0 2 2 2
def memRowD458 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 1 0 2 2 3
  | 1 => tabD45 0 1 0 2 2 4
  | 2 => tabD45 0 1 1 0 0 1
  | 3 => tabD45 0 1 1 0 0 2
  | 4 => tabD45 0 1 1 0 0 3
  | 5 => tabD45 0 1 1 0 0 4
  | 6 => tabD45 0 1 1 0 1 0
  | 7 => tabD45 0 1 1 0 1 2
  | 8 => tabD45 0 1 1 0 1 3
  | 9 => tabD45 0 1 1 0 1 4
  | 10 => tabD45 0 1 1 0 2 0
  | 11 => tabD45 0 1 1 0 2 1
  | 12 => tabD45 0 1 1 0 2 2
  | 13 => tabD45 0 1 1 0 2 4
  | 14 => tabD45 0 1 1 1 0 1
  | 15 => tabD45 0 1 1 1 0 2
  | 16 => tabD45 0 1 1 1 0 3
  | 17 => tabD45 0 1 1 1 0 4
  | 18 => tabD45 0 1 1 1 1 0
  | _ => tabD45 0 1 1 1 1 2
def memRowD459 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 1 1 1 1 3
  | 1 => tabD45 0 1 1 1 1 4
  | 2 => tabD45 0 1 1 1 2 0
  | 3 => tabD45 0 1 1 1 2 1
  | 4 => tabD45 0 1 1 1 2 2
  | 5 => tabD45 0 1 1 1 2 4
  | 6 => tabD45 0 1 1 2 0 0
  | 7 => tabD45 0 1 1 2 0 1
  | 8 => tabD45 0 1 1 2 0 2
  | 9 => tabD45 0 1 1 2 0 3
  | 10 => tabD45 0 1 1 2 0 4
  | 11 => tabD45 0 1 1 2 1 0
  | 12 => tabD45 0 1 1 2 1 1
  | 13 => tabD45 0 1 1 2 1 2
  | 14 => tabD45 0 1 1 2 1 3
  | 15 => tabD45 0 1 1 2 1 4
  | 16 => tabD45 0 1 1 2 2 0
  | 17 => tabD45 0 1 1 2 2 1
  | 18 => tabD45 0 1 1 2 2 2
  | _ => tabD45 0 1 1 2 2 3
def memRowD4510 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 1 1 2 2 4
  | 1 => tabD45 0 1 2 0 0 0
  | 2 => tabD45 0 1 2 0 0 1
  | 3 => tabD45 0 1 2 0 0 2
  | 4 => tabD45 0 1 2 0 0 3
  | 5 => tabD45 0 1 2 0 0 4
  | 6 => tabD45 0 1 2 0 1 0
  | 7 => tabD45 0 1 2 0 1 1
  | 8 => tabD45 0 1 2 0 1 2
  | 9 => tabD45 0 1 2 0 1 3
  | 10 => tabD45 0 1 2 0 1 4
  | 11 => tabD45 0 1 2 0 2 0
  | 12 => tabD45 0 1 2 0 2 1
  | 13 => tabD45 0 1 2 0 2 2
  | 14 => tabD45 0 1 2 0 2 3
  | 15 => tabD45 0 1 2 0 2 4
  | 16 => tabD45 0 1 2 1 0 0
  | 17 => tabD45 0 1 2 1 0 1
  | 18 => tabD45 0 1 2 1 0 2
  | _ => tabD45 0 1 2 1 0 3
def memRowD4511 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 1 2 1 0 4
  | 1 => tabD45 0 1 2 1 1 0
  | 2 => tabD45 0 1 2 1 1 1
  | 3 => tabD45 0 1 2 1 1 2
  | 4 => tabD45 0 1 2 1 1 3
  | 5 => tabD45 0 1 2 1 1 4
  | 6 => tabD45 0 1 2 1 2 0
  | 7 => tabD45 0 1 2 1 2 1
  | 8 => tabD45 0 1 2 1 2 2
  | 9 => tabD45 0 1 2 1 2 3
  | 10 => tabD45 0 1 2 1 2 4
  | 11 => tabD45 0 1 2 2 0 0
  | 12 => tabD45 0 1 2 2 0 1
  | 13 => tabD45 0 1 2 2 0 2
  | 14 => tabD45 0 1 2 2 0 3
  | 15 => tabD45 0 1 2 2 0 4
  | 16 => tabD45 0 1 2 2 1 0
  | 17 => tabD45 0 1 2 2 1 1
  | 18 => tabD45 0 1 2 2 1 2
  | _ => tabD45 0 1 2 2 1 3
def memRowD4512 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 1 2 2 1 4
  | 1 => tabD45 0 1 2 2 2 0
  | 2 => tabD45 0 1 2 2 2 1
  | 3 => tabD45 0 1 2 2 2 2
  | 4 => tabD45 0 1 2 2 2 3
  | 5 => tabD45 0 1 2 2 2 4
  | 6 => tabD45 0 2 0 0 0 0
  | 7 => tabD45 0 2 0 0 0 1
  | 8 => tabD45 0 2 0 0 0 2
  | 9 => tabD45 0 2 0 0 0 3
  | 10 => tabD45 0 2 0 0 0 4
  | 11 => tabD45 0 2 0 0 1 0
  | 12 => tabD45 0 2 0 0 1 1
  | 13 => tabD45 0 2 0 0 1 2
  | 14 => tabD45 0 2 0 0 1 3
  | 15 => tabD45 0 2 0 0 1 4
  | 16 => tabD45 0 2 0 0 2 0
  | 17 => tabD45 0 2 0 0 2 1
  | 18 => tabD45 0 2 0 0 2 2
  | _ => tabD45 0 2 0 0 2 3
def memRowD4513 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 2 0 0 2 4
  | 1 => tabD45 0 2 0 1 0 0
  | 2 => tabD45 0 2 0 1 0 1
  | 3 => tabD45 0 2 0 1 0 2
  | 4 => tabD45 0 2 0 1 0 3
  | 5 => tabD45 0 2 0 1 0 4
  | 6 => tabD45 0 2 0 1 1 0
  | 7 => tabD45 0 2 0 1 1 1
  | 8 => tabD45 0 2 0 1 1 2
  | 9 => tabD45 0 2 0 1 1 3
  | 10 => tabD45 0 2 0 1 1 4
  | 11 => tabD45 0 2 0 1 2 0
  | 12 => tabD45 0 2 0 1 2 1
  | 13 => tabD45 0 2 0 1 2 2
  | 14 => tabD45 0 2 0 1 2 3
  | 15 => tabD45 0 2 0 1 2 4
  | 16 => tabD45 0 2 0 2 0 0
  | 17 => tabD45 0 2 0 2 0 1
  | 18 => tabD45 0 2 0 2 0 2
  | _ => tabD45 0 2 0 2 0 3
def memRowD4514 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 2 0 2 0 4
  | 1 => tabD45 0 2 0 2 1 0
  | 2 => tabD45 0 2 0 2 1 1
  | 3 => tabD45 0 2 0 2 1 2
  | 4 => tabD45 0 2 0 2 1 3
  | 5 => tabD45 0 2 0 2 1 4
  | 6 => tabD45 0 2 0 2 2 0
  | 7 => tabD45 0 2 0 2 2 1
  | 8 => tabD45 0 2 0 2 2 2
  | 9 => tabD45 0 2 0 2 2 3
  | 10 => tabD45 0 2 0 2 2 4
  | 11 => tabD45 0 2 1 0 0 0
  | 12 => tabD45 0 2 1 0 0 1
  | 13 => tabD45 0 2 1 0 0 2
  | 14 => tabD45 0 2 1 0 0 3
  | 15 => tabD45 0 2 1 0 0 4
  | 16 => tabD45 0 2 1 0 1 0
  | 17 => tabD45 0 2 1 0 1 1
  | 18 => tabD45 0 2 1 0 1 2
  | _ => tabD45 0 2 1 0 1 3
def memRowD4515 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 2 1 0 1 4
  | 1 => tabD45 0 2 1 0 2 0
  | 2 => tabD45 0 2 1 0 2 1
  | 3 => tabD45 0 2 1 0 2 2
  | 4 => tabD45 0 2 1 0 2 3
  | 5 => tabD45 0 2 1 0 2 4
  | 6 => tabD45 0 2 1 1 0 0
  | 7 => tabD45 0 2 1 1 0 1
  | 8 => tabD45 0 2 1 1 0 2
  | 9 => tabD45 0 2 1 1 0 3
  | 10 => tabD45 0 2 1 1 0 4
  | 11 => tabD45 0 2 1 1 1 0
  | 12 => tabD45 0 2 1 1 1 1
  | 13 => tabD45 0 2 1 1 1 2
  | 14 => tabD45 0 2 1 1 1 3
  | 15 => tabD45 0 2 1 1 1 4
  | 16 => tabD45 0 2 1 1 2 0
  | 17 => tabD45 0 2 1 1 2 1
  | 18 => tabD45 0 2 1 1 2 2
  | _ => tabD45 0 2 1 1 2 3
def memRowD4516 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 2 1 1 2 4
  | 1 => tabD45 0 2 1 2 0 0
  | 2 => tabD45 0 2 1 2 0 1
  | 3 => tabD45 0 2 1 2 0 2
  | 4 => tabD45 0 2 1 2 0 3
  | 5 => tabD45 0 2 1 2 0 4
  | 6 => tabD45 0 2 1 2 1 0
  | 7 => tabD45 0 2 1 2 1 1
  | 8 => tabD45 0 2 1 2 1 2
  | 9 => tabD45 0 2 1 2 1 3
  | 10 => tabD45 0 2 1 2 1 4
  | 11 => tabD45 0 2 1 2 2 0
  | 12 => tabD45 0 2 1 2 2 1
  | 13 => tabD45 0 2 1 2 2 2
  | 14 => tabD45 0 2 1 2 2 3
  | 15 => tabD45 0 2 1 2 2 4
  | 16 => tabD45 0 2 2 0 0 0
  | 17 => tabD45 0 2 2 0 0 1
  | 18 => tabD45 0 2 2 0 0 2
  | _ => tabD45 0 2 2 0 0 3
def memRowD4517 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 2 2 0 0 4
  | 1 => tabD45 0 2 2 0 1 0
  | 2 => tabD45 0 2 2 0 1 1
  | 3 => tabD45 0 2 2 0 1 2
  | 4 => tabD45 0 2 2 0 1 3
  | 5 => tabD45 0 2 2 0 1 4
  | 6 => tabD45 0 2 2 0 2 0
  | 7 => tabD45 0 2 2 0 2 1
  | 8 => tabD45 0 2 2 0 2 2
  | 9 => tabD45 0 2 2 0 2 3
  | 10 => tabD45 0 2 2 0 2 4
  | 11 => tabD45 0 2 2 1 0 0
  | 12 => tabD45 0 2 2 1 0 1
  | 13 => tabD45 0 2 2 1 0 2
  | 14 => tabD45 0 2 2 1 0 3
  | 15 => tabD45 0 2 2 1 0 4
  | 16 => tabD45 0 2 2 1 1 0
  | 17 => tabD45 0 2 2 1 1 1
  | 18 => tabD45 0 2 2 1 1 2
  | _ => tabD45 0 2 2 1 1 3
def memRowD4518 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD45 0 2 2 1 1 4
  | 1 => tabD45 0 2 2 1 2 0
  | 2 => tabD45 0 2 2 1 2 1
  | 3 => tabD45 0 2 2 1 2 2
  | 4 => tabD45 0 2 2 1 2 3
  | 5 => tabD45 0 2 2 1 2 4
  | 6 => tabD45 0 2 2 2 0 0
  | 7 => tabD45 0 2 2 2 0 1
  | 8 => tabD45 0 2 2 2 0 2
  | 9 => tabD45 0 2 2 2 0 3
  | 10 => tabD45 0 2 2 2 0 4
  | 11 => tabD45 0 2 2 2 1 0
  | 12 => tabD45 0 2 2 2 1 1
  | 13 => tabD45 0 2 2 2 1 2
  | 14 => tabD45 0 2 2 2 1 3
  | 15 => tabD45 0 2 2 2 1 4
  | 16 => tabD45 0 2 2 2 2 0
  | 17 => tabD45 0 2 2 2 2 1
  | 18 => tabD45 0 2 2 2 2 2
  | _ => tabD45 0 2 2 2 2 3
def memRowD4519 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | _ => tabD45 0 2 2 2 2 4
def memD45 (i : Fin 381) : Fin 5 → Fin 5 → Fin 5 :=
  match (i.1 / 20 : Nat) with
  | 0 => memRowD450 ⟨i.1 % 20, by omega⟩
  | 1 => memRowD451 ⟨i.1 % 20, by omega⟩
  | 2 => memRowD452 ⟨i.1 % 20, by omega⟩
  | 3 => memRowD453 ⟨i.1 % 20, by omega⟩
  | 4 => memRowD454 ⟨i.1 % 20, by omega⟩
  | 5 => memRowD455 ⟨i.1 % 20, by omega⟩
  | 6 => memRowD456 ⟨i.1 % 20, by omega⟩
  | 7 => memRowD457 ⟨i.1 % 20, by omega⟩
  | 8 => memRowD458 ⟨i.1 % 20, by omega⟩
  | 9 => memRowD459 ⟨i.1 % 20, by omega⟩
  | 10 => memRowD4510 ⟨i.1 % 20, by omega⟩
  | 11 => memRowD4511 ⟨i.1 % 20, by omega⟩
  | 12 => memRowD4512 ⟨i.1 % 20, by omega⟩
  | 13 => memRowD4513 ⟨i.1 % 20, by omega⟩
  | 14 => memRowD4514 ⟨i.1 % 20, by omega⟩
  | 15 => memRowD4515 ⟨i.1 % 20, by omega⟩
  | 16 => memRowD4516 ⟨i.1 % 20, by omega⟩
  | 17 => memRowD4517 ⟨i.1 % 20, by omega⟩
  | 18 => memRowD4518 ⟨i.1 % 20, by omega⟩
  | _ => memRowD4519 ⟨i.1 % 20, by omega⟩

/-- Which of the `381` members a given invariant tuple is, so that `mem_of_isExactD45` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD45 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 0, 11, 0, 12, 13, 14, 15, 16, 0, 17, 18, 19, 20, 21,
  22, 0, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 0, 39, 40, 41, 42, 43,
  0, 44, 45, 46, 47, 48, 49, 0, 50, 0, 51, 52, 53, 54, 55, 0, 56, 57, 58, 59, 60, 61, 0, 62, 63,
  64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
  88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
  109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 0, 123, 124, 125, 126,
  127, 0, 128, 129, 130, 131, 132, 133, 0, 134, 0, 135, 136, 137, 138, 139, 0, 140, 141, 142,
  143, 144, 145, 0, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
  161, 0, 162, 163, 164, 165, 166, 0, 167, 168, 169, 170, 171, 172, 0, 173, 0, 174, 175, 176,
  177, 178, 0, 179, 180, 181, 182, 183, 184, 0, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194,
  195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213,
  214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232,
  233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251,
  252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270,
  271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
  290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308,
  309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327,
  328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346,
  347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365,
  366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380]

/-- The arguments as one mixed-radix index, which is how `rankArrD45` is addressed. -/
def encTD45 (a : Fin 1) (b c d e : Fin 3) (f : Fin 5) : Nat :=
  a.1 * 405 +
    b.1 * 135 +
    c.1 * 45 +
    d.1 * 15 +
    e.1 * 5 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD45 (a : Fin 1) (b c d e : Fin 3) (f : Fin 5) : Fin 381 :=
  ⟨min (rankArrD45.getD (encTD45 a b c d e f) 0) 380, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD45 (i : Fin 381) : Magma (Fin 5) := Magma.mk (memD45 i)

theorem exactD45_isEndo (i : Fin 381) (j : Fin 8) : (exactD45 i).IsEndo ⇑(eED45 j) := by
  simp only [eED45, coe_permOf]; revert i j; native_decide

theorem exactD45_not_isEndo (i : Fin 381) (j : Fin 1) : ¬ (exactD45 i).IsEndo ⇑(eXD45 j) := by
  simp only [eXD45, coe_permOf]; revert i j; native_decide

/-- `rankD45` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD45` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD45 (a : Fin 1) (b c d e : Fin 3) (f : Fin 5)
    (h : Magma.isExact (tabD45 a b c d e f) permED45 permXD45 = true) :
    memD45 (rankD45 a b c d e f) = tabD45 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `381`
listed members. -/
theorem mem_of_isExactD45 (a : Fin 1) (b c d e : Fin 3) (f : Fin 5)
    (h : Magma.isExact (tabD45 a b c d e f) permED45 permXD45 = true) :
    ∃ i, memD45 i = tabD45 a b c d e f :=
  ⟨_, mem_rankD45 a b c d e f h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD45`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD45` turns that into a member index. -/
theorem exists_exactD45 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eED45 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD45 i)) : ∃ i, exactD45 i = M := by
  simp only [eED45, coe_permOf] at hE
  simp only [eXD45, coe_permOf] at hX
  have hop : M.op = Magma.transport permED45 trD45 (fun i ↦ M.op (repD45 i).1 (repD45 i).2) :=
    Magma.op_eq_transport (rep := repD45) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED45) (idx := stabIdxD450) (a := (repD45 0).1) (b := (repD45 0).2)
    (val := valD450) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED45) (idx := stabIdxD451) (a := (repD45 1).1) (b := (repD45 1).2)
    (val := valD451) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED45) (idx := stabIdxD452) (a := (repD45 2).1) (b := (repD45 2).2)
    (val := valD452) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permED45) (idx := stabIdxD453) (a := (repD45 3).1) (b := (repD45 3).2)
    (val := valD453) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permED45) (idx := stabIdxD454) (a := (repD45 4).1) (b := (repD45 4).2)
    (val := valD454) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permED45) (idx := stabIdxD455) (a := (repD45 5).1) (b := (repD45 5).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decD45 a b c d e f = fun i ↦ M.op (repD45 i).1 (repD45 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabD45 a b c d e f = M.op := by
    rw [tabD45_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD45 a b c d e f) permED45 permXD45 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD45 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`8` group of `Magma.permED45`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD45 {L L' : Law.NatMagmaLaw} {i : Fin 381}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactD45 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactD45 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD45 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD45
    (fun k ↦ (Magma.exactD45_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD45_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
