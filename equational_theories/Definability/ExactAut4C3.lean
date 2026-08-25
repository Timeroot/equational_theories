import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `C3` on `Fin 4`

One class of `Definability/ExactAut4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`3` group `⟨(1 2 3)⟩` -/

/-- The `3` elements of the group: `()`, `(1 2 3)`, `(1 3 2)`. -/
def pEC30 : Fin 4 → Fin 4 := id
def pEC31 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1
def pEC32 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2

def permEC3 : Fin 3 → Fin 4 → Fin 4
  | 0 => pEC30
  | 1 => pEC31
  | 2 => pEC32

def permEinvC3 : Fin 3 → Fin 4 → Fin 4
  | 0 => pEC30
  | 1 => pEC32
  | 2 => pEC31

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEC3 (i : Fin 3) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permEC3 i) (permEinvC3 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(1 2)`, `(0 3)(1 2)`. Every subgroup
properly containing the group above contains one of them, so a magma admitting the group and not
these has that group as its automorphism group exactly. -/
def pXC30 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pXC31 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0
def pXC30inv : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pXC31inv : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permXC3 : Fin 2 → Fin 4 → Fin 4
  | 0 => pXC30
  | 1 => pXC31

def permXinvC3 : Fin 2 → Fin 4 → Fin 4
  | 0 => pXC30inv
  | 1 => pXC31inv

def eXC3 (i : Fin 2) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permXC3 i) (permXinvC3 i) (by revert i; decide)

/-- One representative per orbit of the group on the `16` cells; there are `6`, so an invariant
operation is `6` values. -/
def repC3 : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)
  | 5 => (1, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trC3 : Fin 4 → Fin 4 → Fin 6 × Fin 3
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (5, 0)
  | 2, 0 => (2, 1)
  | 2, 1 => (5, 1)
  | 2, 2 => (3, 1)
  | 2, 3 => (4, 1)
  | 3, 0 => (2, 2)
  | 3, 1 => (4, 2)
  | 3, 2 => (5, 2)
  | 3, 3 => (3, 2)

/-- The `3` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxC30 : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valC30 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxC31 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxC32 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxC33 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxC34 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxC35 : Fin 1 → Fin 3
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def decC3 (a : Fin 1) (b c d e f : Fin 4) : Fin 6 → Fin 4
  | 0 => valC30 a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabC3_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabC3 (a : Fin 1) (b c d e f : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => valC30 a
  | 0, 1 => b
  | 0, 2 => pEC31 b
  | 0, 3 => pEC32 b
  | 1, 0 => c
  | 1, 1 => d
  | 1, 2 => e
  | 1, 3 => f
  | 2, 0 => pEC31 c
  | 2, 1 => pEC31 f
  | 2, 2 => pEC31 d
  | 2, 3 => pEC31 e
  | 3, 0 => pEC32 c
  | 3, 1 => pEC32 e
  | 3, 2 => pEC32 f
  | 3, 3 => pEC32 d

theorem tabC3_eq_transport (a : Fin 1) (b c d e f : Fin 4) :
    tabC3 a b c d e f = Magma.transport permEC3 trC3 (decC3 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `990` magmas on `Fin 4` whose automorphism group is exactly this group, listed under one
index. Of the `1024` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowC30 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 0 0 0 1
  | 1 => tabC3 0 0 0 0 0 2
  | 2 => tabC3 0 0 0 0 0 3
  | 3 => tabC3 0 0 0 0 1 0
  | 4 => tabC3 0 0 0 0 1 2
  | 5 => tabC3 0 0 0 0 1 3
  | 6 => tabC3 0 0 0 0 2 0
  | 7 => tabC3 0 0 0 0 2 1
  | 8 => tabC3 0 0 0 0 2 2
  | 9 => tabC3 0 0 0 0 3 0
  | 10 => tabC3 0 0 0 0 3 1
  | 11 => tabC3 0 0 0 0 3 3
  | 12 => tabC3 0 0 0 1 0 1
  | 13 => tabC3 0 0 0 1 0 2
  | 14 => tabC3 0 0 0 1 0 3
  | 15 => tabC3 0 0 0 1 1 0
  | 16 => tabC3 0 0 0 1 1 2
  | 17 => tabC3 0 0 0 1 1 3
  | 18 => tabC3 0 0 0 1 2 0
  | 19 => tabC3 0 0 0 1 2 1
  | 20 => tabC3 0 0 0 1 2 2
  | 21 => tabC3 0 0 0 1 3 0
  | 22 => tabC3 0 0 0 1 3 1
  | 23 => tabC3 0 0 0 1 3 3
  | 24 => tabC3 0 0 0 2 0 0
  | 25 => tabC3 0 0 0 2 0 1
  | 26 => tabC3 0 0 0 2 0 2
  | 27 => tabC3 0 0 0 2 0 3
  | 28 => tabC3 0 0 0 2 1 0
  | 29 => tabC3 0 0 0 2 1 1
  | 30 => tabC3 0 0 0 2 1 2
  | _ => tabC3 0 0 0 2 1 3
def memRowC31 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 0 2 2 0
  | 1 => tabC3 0 0 0 2 2 1
  | 2 => tabC3 0 0 0 2 2 2
  | 3 => tabC3 0 0 0 2 2 3
  | 4 => tabC3 0 0 0 2 3 0
  | 5 => tabC3 0 0 0 2 3 1
  | 6 => tabC3 0 0 0 2 3 2
  | 7 => tabC3 0 0 0 2 3 3
  | 8 => tabC3 0 0 0 3 0 0
  | 9 => tabC3 0 0 0 3 0 1
  | 10 => tabC3 0 0 0 3 0 2
  | 11 => tabC3 0 0 0 3 0 3
  | 12 => tabC3 0 0 0 3 1 0
  | 13 => tabC3 0 0 0 3 1 1
  | 14 => tabC3 0 0 0 3 1 2
  | 15 => tabC3 0 0 0 3 1 3
  | 16 => tabC3 0 0 0 3 2 0
  | 17 => tabC3 0 0 0 3 2 1
  | 18 => tabC3 0 0 0 3 2 2
  | 19 => tabC3 0 0 0 3 2 3
  | 20 => tabC3 0 0 0 3 3 0
  | 21 => tabC3 0 0 0 3 3 1
  | 22 => tabC3 0 0 0 3 3 2
  | 23 => tabC3 0 0 0 3 3 3
  | 24 => tabC3 0 0 1 0 0 1
  | 25 => tabC3 0 0 1 0 0 2
  | 26 => tabC3 0 0 1 0 0 3
  | 27 => tabC3 0 0 1 0 1 0
  | 28 => tabC3 0 0 1 0 1 2
  | 29 => tabC3 0 0 1 0 1 3
  | 30 => tabC3 0 0 1 0 2 0
  | _ => tabC3 0 0 1 0 2 1
def memRowC32 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 1 0 2 2
  | 1 => tabC3 0 0 1 0 3 0
  | 2 => tabC3 0 0 1 0 3 1
  | 3 => tabC3 0 0 1 0 3 3
  | 4 => tabC3 0 0 1 1 0 1
  | 5 => tabC3 0 0 1 1 0 2
  | 6 => tabC3 0 0 1 1 0 3
  | 7 => tabC3 0 0 1 1 1 0
  | 8 => tabC3 0 0 1 1 1 2
  | 9 => tabC3 0 0 1 1 1 3
  | 10 => tabC3 0 0 1 1 2 0
  | 11 => tabC3 0 0 1 1 2 1
  | 12 => tabC3 0 0 1 1 2 2
  | 13 => tabC3 0 0 1 1 3 0
  | 14 => tabC3 0 0 1 1 3 1
  | 15 => tabC3 0 0 1 1 3 3
  | 16 => tabC3 0 0 1 2 0 0
  | 17 => tabC3 0 0 1 2 0 1
  | 18 => tabC3 0 0 1 2 0 2
  | 19 => tabC3 0 0 1 2 0 3
  | 20 => tabC3 0 0 1 2 1 0
  | 21 => tabC3 0 0 1 2 1 1
  | 22 => tabC3 0 0 1 2 1 2
  | 23 => tabC3 0 0 1 2 1 3
  | 24 => tabC3 0 0 1 2 2 0
  | 25 => tabC3 0 0 1 2 2 1
  | 26 => tabC3 0 0 1 2 2 2
  | 27 => tabC3 0 0 1 2 2 3
  | 28 => tabC3 0 0 1 2 3 0
  | 29 => tabC3 0 0 1 2 3 1
  | 30 => tabC3 0 0 1 2 3 2
  | _ => tabC3 0 0 1 2 3 3
def memRowC33 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 1 3 0 0
  | 1 => tabC3 0 0 1 3 0 1
  | 2 => tabC3 0 0 1 3 0 2
  | 3 => tabC3 0 0 1 3 0 3
  | 4 => tabC3 0 0 1 3 1 0
  | 5 => tabC3 0 0 1 3 1 1
  | 6 => tabC3 0 0 1 3 1 2
  | 7 => tabC3 0 0 1 3 1 3
  | 8 => tabC3 0 0 1 3 2 0
  | 9 => tabC3 0 0 1 3 2 1
  | 10 => tabC3 0 0 1 3 2 2
  | 11 => tabC3 0 0 1 3 2 3
  | 12 => tabC3 0 0 1 3 3 0
  | 13 => tabC3 0 0 1 3 3 1
  | 14 => tabC3 0 0 1 3 3 2
  | 15 => tabC3 0 0 1 3 3 3
  | 16 => tabC3 0 0 2 0 0 0
  | 17 => tabC3 0 0 2 0 0 1
  | 18 => tabC3 0 0 2 0 0 2
  | 19 => tabC3 0 0 2 0 0 3
  | 20 => tabC3 0 0 2 0 1 0
  | 21 => tabC3 0 0 2 0 1 1
  | 22 => tabC3 0 0 2 0 1 2
  | 23 => tabC3 0 0 2 0 1 3
  | 24 => tabC3 0 0 2 0 2 0
  | 25 => tabC3 0 0 2 0 2 1
  | 26 => tabC3 0 0 2 0 2 2
  | 27 => tabC3 0 0 2 0 2 3
  | 28 => tabC3 0 0 2 0 3 0
  | 29 => tabC3 0 0 2 0 3 1
  | 30 => tabC3 0 0 2 0 3 2
  | _ => tabC3 0 0 2 0 3 3
def memRowC34 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 2 1 0 0
  | 1 => tabC3 0 0 2 1 0 1
  | 2 => tabC3 0 0 2 1 0 2
  | 3 => tabC3 0 0 2 1 0 3
  | 4 => tabC3 0 0 2 1 1 0
  | 5 => tabC3 0 0 2 1 1 1
  | 6 => tabC3 0 0 2 1 1 2
  | 7 => tabC3 0 0 2 1 1 3
  | 8 => tabC3 0 0 2 1 2 0
  | 9 => tabC3 0 0 2 1 2 1
  | 10 => tabC3 0 0 2 1 2 2
  | 11 => tabC3 0 0 2 1 2 3
  | 12 => tabC3 0 0 2 1 3 0
  | 13 => tabC3 0 0 2 1 3 1
  | 14 => tabC3 0 0 2 1 3 2
  | 15 => tabC3 0 0 2 1 3 3
  | 16 => tabC3 0 0 2 2 0 0
  | 17 => tabC3 0 0 2 2 0 1
  | 18 => tabC3 0 0 2 2 0 2
  | 19 => tabC3 0 0 2 2 0 3
  | 20 => tabC3 0 0 2 2 1 0
  | 21 => tabC3 0 0 2 2 1 1
  | 22 => tabC3 0 0 2 2 1 2
  | 23 => tabC3 0 0 2 2 1 3
  | 24 => tabC3 0 0 2 2 2 0
  | 25 => tabC3 0 0 2 2 2 1
  | 26 => tabC3 0 0 2 2 2 2
  | 27 => tabC3 0 0 2 2 2 3
  | 28 => tabC3 0 0 2 2 3 0
  | 29 => tabC3 0 0 2 2 3 1
  | 30 => tabC3 0 0 2 2 3 2
  | _ => tabC3 0 0 2 2 3 3
def memRowC35 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 2 3 0 0
  | 1 => tabC3 0 0 2 3 0 1
  | 2 => tabC3 0 0 2 3 0 2
  | 3 => tabC3 0 0 2 3 0 3
  | 4 => tabC3 0 0 2 3 1 0
  | 5 => tabC3 0 0 2 3 1 1
  | 6 => tabC3 0 0 2 3 1 2
  | 7 => tabC3 0 0 2 3 1 3
  | 8 => tabC3 0 0 2 3 2 0
  | 9 => tabC3 0 0 2 3 2 1
  | 10 => tabC3 0 0 2 3 2 2
  | 11 => tabC3 0 0 2 3 2 3
  | 12 => tabC3 0 0 2 3 3 0
  | 13 => tabC3 0 0 2 3 3 1
  | 14 => tabC3 0 0 2 3 3 2
  | 15 => tabC3 0 0 2 3 3 3
  | 16 => tabC3 0 0 3 0 0 0
  | 17 => tabC3 0 0 3 0 0 1
  | 18 => tabC3 0 0 3 0 0 2
  | 19 => tabC3 0 0 3 0 0 3
  | 20 => tabC3 0 0 3 0 1 0
  | 21 => tabC3 0 0 3 0 1 1
  | 22 => tabC3 0 0 3 0 1 2
  | 23 => tabC3 0 0 3 0 1 3
  | 24 => tabC3 0 0 3 0 2 0
  | 25 => tabC3 0 0 3 0 2 1
  | 26 => tabC3 0 0 3 0 2 2
  | 27 => tabC3 0 0 3 0 2 3
  | 28 => tabC3 0 0 3 0 3 0
  | 29 => tabC3 0 0 3 0 3 1
  | 30 => tabC3 0 0 3 0 3 2
  | _ => tabC3 0 0 3 0 3 3
def memRowC36 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 3 1 0 0
  | 1 => tabC3 0 0 3 1 0 1
  | 2 => tabC3 0 0 3 1 0 2
  | 3 => tabC3 0 0 3 1 0 3
  | 4 => tabC3 0 0 3 1 1 0
  | 5 => tabC3 0 0 3 1 1 1
  | 6 => tabC3 0 0 3 1 1 2
  | 7 => tabC3 0 0 3 1 1 3
  | 8 => tabC3 0 0 3 1 2 0
  | 9 => tabC3 0 0 3 1 2 1
  | 10 => tabC3 0 0 3 1 2 2
  | 11 => tabC3 0 0 3 1 2 3
  | 12 => tabC3 0 0 3 1 3 0
  | 13 => tabC3 0 0 3 1 3 1
  | 14 => tabC3 0 0 3 1 3 2
  | 15 => tabC3 0 0 3 1 3 3
  | 16 => tabC3 0 0 3 2 0 0
  | 17 => tabC3 0 0 3 2 0 1
  | 18 => tabC3 0 0 3 2 0 2
  | 19 => tabC3 0 0 3 2 0 3
  | 20 => tabC3 0 0 3 2 1 0
  | 21 => tabC3 0 0 3 2 1 1
  | 22 => tabC3 0 0 3 2 1 2
  | 23 => tabC3 0 0 3 2 1 3
  | 24 => tabC3 0 0 3 2 2 0
  | 25 => tabC3 0 0 3 2 2 1
  | 26 => tabC3 0 0 3 2 2 2
  | 27 => tabC3 0 0 3 2 2 3
  | 28 => tabC3 0 0 3 2 3 0
  | 29 => tabC3 0 0 3 2 3 1
  | 30 => tabC3 0 0 3 2 3 2
  | _ => tabC3 0 0 3 2 3 3
def memRowC37 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 0 3 3 0 0
  | 1 => tabC3 0 0 3 3 0 1
  | 2 => tabC3 0 0 3 3 0 2
  | 3 => tabC3 0 0 3 3 0 3
  | 4 => tabC3 0 0 3 3 1 0
  | 5 => tabC3 0 0 3 3 1 1
  | 6 => tabC3 0 0 3 3 1 2
  | 7 => tabC3 0 0 3 3 1 3
  | 8 => tabC3 0 0 3 3 2 0
  | 9 => tabC3 0 0 3 3 2 1
  | 10 => tabC3 0 0 3 3 2 2
  | 11 => tabC3 0 0 3 3 2 3
  | 12 => tabC3 0 0 3 3 3 0
  | 13 => tabC3 0 0 3 3 3 1
  | 14 => tabC3 0 0 3 3 3 2
  | 15 => tabC3 0 0 3 3 3 3
  | 16 => tabC3 0 1 0 0 0 1
  | 17 => tabC3 0 1 0 0 0 2
  | 18 => tabC3 0 1 0 0 0 3
  | 19 => tabC3 0 1 0 0 1 0
  | 20 => tabC3 0 1 0 0 1 2
  | 21 => tabC3 0 1 0 0 1 3
  | 22 => tabC3 0 1 0 0 2 0
  | 23 => tabC3 0 1 0 0 2 1
  | 24 => tabC3 0 1 0 0 2 2
  | 25 => tabC3 0 1 0 0 3 0
  | 26 => tabC3 0 1 0 0 3 1
  | 27 => tabC3 0 1 0 0 3 3
  | 28 => tabC3 0 1 0 1 0 1
  | 29 => tabC3 0 1 0 1 0 2
  | 30 => tabC3 0 1 0 1 0 3
  | _ => tabC3 0 1 0 1 1 0
def memRowC38 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 0 1 1 2
  | 1 => tabC3 0 1 0 1 1 3
  | 2 => tabC3 0 1 0 1 2 0
  | 3 => tabC3 0 1 0 1 2 1
  | 4 => tabC3 0 1 0 1 2 2
  | 5 => tabC3 0 1 0 1 3 0
  | 6 => tabC3 0 1 0 1 3 1
  | 7 => tabC3 0 1 0 1 3 3
  | 8 => tabC3 0 1 0 2 0 0
  | 9 => tabC3 0 1 0 2 0 1
  | 10 => tabC3 0 1 0 2 0 2
  | 11 => tabC3 0 1 0 2 0 3
  | 12 => tabC3 0 1 0 2 1 0
  | 13 => tabC3 0 1 0 2 1 1
  | 14 => tabC3 0 1 0 2 1 2
  | 15 => tabC3 0 1 0 2 1 3
  | 16 => tabC3 0 1 0 2 2 0
  | 17 => tabC3 0 1 0 2 2 1
  | 18 => tabC3 0 1 0 2 2 2
  | 19 => tabC3 0 1 0 2 2 3
  | 20 => tabC3 0 1 0 2 3 0
  | 21 => tabC3 0 1 0 2 3 1
  | 22 => tabC3 0 1 0 2 3 2
  | 23 => tabC3 0 1 0 2 3 3
  | 24 => tabC3 0 1 0 3 0 0
  | 25 => tabC3 0 1 0 3 0 1
  | 26 => tabC3 0 1 0 3 0 2
  | 27 => tabC3 0 1 0 3 0 3
  | 28 => tabC3 0 1 0 3 1 0
  | 29 => tabC3 0 1 0 3 1 1
  | 30 => tabC3 0 1 0 3 1 2
  | _ => tabC3 0 1 0 3 1 3
def memRowC39 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 0 3 2 0
  | 1 => tabC3 0 1 0 3 2 1
  | 2 => tabC3 0 1 0 3 2 2
  | 3 => tabC3 0 1 0 3 2 3
  | 4 => tabC3 0 1 0 3 3 0
  | 5 => tabC3 0 1 0 3 3 1
  | 6 => tabC3 0 1 0 3 3 2
  | 7 => tabC3 0 1 0 3 3 3
  | 8 => tabC3 0 1 1 0 0 1
  | 9 => tabC3 0 1 1 0 0 2
  | 10 => tabC3 0 1 1 0 0 3
  | 11 => tabC3 0 1 1 0 1 0
  | 12 => tabC3 0 1 1 0 1 2
  | 13 => tabC3 0 1 1 0 1 3
  | 14 => tabC3 0 1 1 0 2 0
  | 15 => tabC3 0 1 1 0 2 1
  | 16 => tabC3 0 1 1 0 2 2
  | 17 => tabC3 0 1 1 0 3 0
  | 18 => tabC3 0 1 1 0 3 1
  | 19 => tabC3 0 1 1 0 3 3
  | 20 => tabC3 0 1 1 1 0 1
  | 21 => tabC3 0 1 1 1 0 2
  | 22 => tabC3 0 1 1 1 0 3
  | 23 => tabC3 0 1 1 1 1 0
  | 24 => tabC3 0 1 1 1 1 2
  | 25 => tabC3 0 1 1 1 1 3
  | 26 => tabC3 0 1 1 1 2 0
  | 27 => tabC3 0 1 1 1 2 1
  | 28 => tabC3 0 1 1 1 2 2
  | 29 => tabC3 0 1 1 1 3 0
  | 30 => tabC3 0 1 1 1 3 1
  | _ => tabC3 0 1 1 1 3 3
def memRowC310 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 1 2 0 0
  | 1 => tabC3 0 1 1 2 0 1
  | 2 => tabC3 0 1 1 2 0 2
  | 3 => tabC3 0 1 1 2 0 3
  | 4 => tabC3 0 1 1 2 1 0
  | 5 => tabC3 0 1 1 2 1 1
  | 6 => tabC3 0 1 1 2 1 2
  | 7 => tabC3 0 1 1 2 1 3
  | 8 => tabC3 0 1 1 2 2 0
  | 9 => tabC3 0 1 1 2 2 1
  | 10 => tabC3 0 1 1 2 2 2
  | 11 => tabC3 0 1 1 2 2 3
  | 12 => tabC3 0 1 1 2 3 0
  | 13 => tabC3 0 1 1 2 3 1
  | 14 => tabC3 0 1 1 2 3 2
  | 15 => tabC3 0 1 1 2 3 3
  | 16 => tabC3 0 1 1 3 0 0
  | 17 => tabC3 0 1 1 3 0 1
  | 18 => tabC3 0 1 1 3 0 2
  | 19 => tabC3 0 1 1 3 0 3
  | 20 => tabC3 0 1 1 3 1 0
  | 21 => tabC3 0 1 1 3 1 1
  | 22 => tabC3 0 1 1 3 1 2
  | 23 => tabC3 0 1 1 3 1 3
  | 24 => tabC3 0 1 1 3 2 0
  | 25 => tabC3 0 1 1 3 2 1
  | 26 => tabC3 0 1 1 3 2 2
  | 27 => tabC3 0 1 1 3 2 3
  | 28 => tabC3 0 1 1 3 3 0
  | 29 => tabC3 0 1 1 3 3 1
  | 30 => tabC3 0 1 1 3 3 2
  | _ => tabC3 0 1 1 3 3 3
def memRowC311 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 2 0 0 0
  | 1 => tabC3 0 1 2 0 0 1
  | 2 => tabC3 0 1 2 0 0 2
  | 3 => tabC3 0 1 2 0 0 3
  | 4 => tabC3 0 1 2 0 1 0
  | 5 => tabC3 0 1 2 0 1 1
  | 6 => tabC3 0 1 2 0 1 2
  | 7 => tabC3 0 1 2 0 1 3
  | 8 => tabC3 0 1 2 0 2 0
  | 9 => tabC3 0 1 2 0 2 1
  | 10 => tabC3 0 1 2 0 2 2
  | 11 => tabC3 0 1 2 0 2 3
  | 12 => tabC3 0 1 2 0 3 0
  | 13 => tabC3 0 1 2 0 3 1
  | 14 => tabC3 0 1 2 0 3 2
  | 15 => tabC3 0 1 2 0 3 3
  | 16 => tabC3 0 1 2 1 0 0
  | 17 => tabC3 0 1 2 1 0 1
  | 18 => tabC3 0 1 2 1 0 2
  | 19 => tabC3 0 1 2 1 0 3
  | 20 => tabC3 0 1 2 1 1 0
  | 21 => tabC3 0 1 2 1 1 1
  | 22 => tabC3 0 1 2 1 1 2
  | 23 => tabC3 0 1 2 1 1 3
  | 24 => tabC3 0 1 2 1 2 0
  | 25 => tabC3 0 1 2 1 2 1
  | 26 => tabC3 0 1 2 1 2 2
  | 27 => tabC3 0 1 2 1 2 3
  | 28 => tabC3 0 1 2 1 3 0
  | 29 => tabC3 0 1 2 1 3 1
  | 30 => tabC3 0 1 2 1 3 2
  | _ => tabC3 0 1 2 1 3 3
def memRowC312 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 2 2 0 0
  | 1 => tabC3 0 1 2 2 0 1
  | 2 => tabC3 0 1 2 2 0 2
  | 3 => tabC3 0 1 2 2 0 3
  | 4 => tabC3 0 1 2 2 1 0
  | 5 => tabC3 0 1 2 2 1 1
  | 6 => tabC3 0 1 2 2 1 2
  | 7 => tabC3 0 1 2 2 1 3
  | 8 => tabC3 0 1 2 2 2 0
  | 9 => tabC3 0 1 2 2 2 1
  | 10 => tabC3 0 1 2 2 2 2
  | 11 => tabC3 0 1 2 2 2 3
  | 12 => tabC3 0 1 2 2 3 0
  | 13 => tabC3 0 1 2 2 3 1
  | 14 => tabC3 0 1 2 2 3 2
  | 15 => tabC3 0 1 2 2 3 3
  | 16 => tabC3 0 1 2 3 0 0
  | 17 => tabC3 0 1 2 3 0 1
  | 18 => tabC3 0 1 2 3 0 2
  | 19 => tabC3 0 1 2 3 0 3
  | 20 => tabC3 0 1 2 3 1 0
  | 21 => tabC3 0 1 2 3 1 1
  | 22 => tabC3 0 1 2 3 1 2
  | 23 => tabC3 0 1 2 3 1 3
  | 24 => tabC3 0 1 2 3 2 0
  | 25 => tabC3 0 1 2 3 2 1
  | 26 => tabC3 0 1 2 3 2 2
  | 27 => tabC3 0 1 2 3 2 3
  | 28 => tabC3 0 1 2 3 3 0
  | 29 => tabC3 0 1 2 3 3 1
  | 30 => tabC3 0 1 2 3 3 2
  | _ => tabC3 0 1 2 3 3 3
def memRowC313 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 3 0 0 0
  | 1 => tabC3 0 1 3 0 0 1
  | 2 => tabC3 0 1 3 0 0 2
  | 3 => tabC3 0 1 3 0 0 3
  | 4 => tabC3 0 1 3 0 1 0
  | 5 => tabC3 0 1 3 0 1 1
  | 6 => tabC3 0 1 3 0 1 2
  | 7 => tabC3 0 1 3 0 1 3
  | 8 => tabC3 0 1 3 0 2 0
  | 9 => tabC3 0 1 3 0 2 1
  | 10 => tabC3 0 1 3 0 2 2
  | 11 => tabC3 0 1 3 0 2 3
  | 12 => tabC3 0 1 3 0 3 0
  | 13 => tabC3 0 1 3 0 3 1
  | 14 => tabC3 0 1 3 0 3 2
  | 15 => tabC3 0 1 3 0 3 3
  | 16 => tabC3 0 1 3 1 0 0
  | 17 => tabC3 0 1 3 1 0 1
  | 18 => tabC3 0 1 3 1 0 2
  | 19 => tabC3 0 1 3 1 0 3
  | 20 => tabC3 0 1 3 1 1 0
  | 21 => tabC3 0 1 3 1 1 1
  | 22 => tabC3 0 1 3 1 1 2
  | 23 => tabC3 0 1 3 1 1 3
  | 24 => tabC3 0 1 3 1 2 0
  | 25 => tabC3 0 1 3 1 2 1
  | 26 => tabC3 0 1 3 1 2 2
  | 27 => tabC3 0 1 3 1 2 3
  | 28 => tabC3 0 1 3 1 3 0
  | 29 => tabC3 0 1 3 1 3 1
  | 30 => tabC3 0 1 3 1 3 2
  | _ => tabC3 0 1 3 1 3 3
def memRowC314 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 1 3 2 0 0
  | 1 => tabC3 0 1 3 2 0 1
  | 2 => tabC3 0 1 3 2 0 2
  | 3 => tabC3 0 1 3 2 0 3
  | 4 => tabC3 0 1 3 2 1 0
  | 5 => tabC3 0 1 3 2 1 1
  | 6 => tabC3 0 1 3 2 1 2
  | 7 => tabC3 0 1 3 2 1 3
  | 8 => tabC3 0 1 3 2 2 0
  | 9 => tabC3 0 1 3 2 2 1
  | 10 => tabC3 0 1 3 2 2 2
  | 11 => tabC3 0 1 3 2 2 3
  | 12 => tabC3 0 1 3 2 3 0
  | 13 => tabC3 0 1 3 2 3 1
  | 14 => tabC3 0 1 3 2 3 2
  | 15 => tabC3 0 1 3 2 3 3
  | 16 => tabC3 0 1 3 3 0 0
  | 17 => tabC3 0 1 3 3 0 1
  | 18 => tabC3 0 1 3 3 0 2
  | 19 => tabC3 0 1 3 3 0 3
  | 20 => tabC3 0 1 3 3 1 0
  | 21 => tabC3 0 1 3 3 1 1
  | 22 => tabC3 0 1 3 3 1 2
  | 23 => tabC3 0 1 3 3 1 3
  | 24 => tabC3 0 1 3 3 2 0
  | 25 => tabC3 0 1 3 3 2 1
  | 26 => tabC3 0 1 3 3 2 2
  | 27 => tabC3 0 1 3 3 2 3
  | 28 => tabC3 0 1 3 3 3 0
  | 29 => tabC3 0 1 3 3 3 1
  | 30 => tabC3 0 1 3 3 3 2
  | _ => tabC3 0 1 3 3 3 3
def memRowC315 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 0 0 0 0
  | 1 => tabC3 0 2 0 0 0 1
  | 2 => tabC3 0 2 0 0 0 2
  | 3 => tabC3 0 2 0 0 0 3
  | 4 => tabC3 0 2 0 0 1 0
  | 5 => tabC3 0 2 0 0 1 1
  | 6 => tabC3 0 2 0 0 1 2
  | 7 => tabC3 0 2 0 0 1 3
  | 8 => tabC3 0 2 0 0 2 0
  | 9 => tabC3 0 2 0 0 2 1
  | 10 => tabC3 0 2 0 0 2 2
  | 11 => tabC3 0 2 0 0 2 3
  | 12 => tabC3 0 2 0 0 3 0
  | 13 => tabC3 0 2 0 0 3 1
  | 14 => tabC3 0 2 0 0 3 2
  | 15 => tabC3 0 2 0 0 3 3
  | 16 => tabC3 0 2 0 1 0 0
  | 17 => tabC3 0 2 0 1 0 1
  | 18 => tabC3 0 2 0 1 0 2
  | 19 => tabC3 0 2 0 1 0 3
  | 20 => tabC3 0 2 0 1 1 0
  | 21 => tabC3 0 2 0 1 1 1
  | 22 => tabC3 0 2 0 1 1 2
  | 23 => tabC3 0 2 0 1 1 3
  | 24 => tabC3 0 2 0 1 2 0
  | 25 => tabC3 0 2 0 1 2 1
  | 26 => tabC3 0 2 0 1 2 2
  | 27 => tabC3 0 2 0 1 2 3
  | 28 => tabC3 0 2 0 1 3 0
  | 29 => tabC3 0 2 0 1 3 1
  | 30 => tabC3 0 2 0 1 3 2
  | _ => tabC3 0 2 0 1 3 3
def memRowC316 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 0 2 0 0
  | 1 => tabC3 0 2 0 2 0 1
  | 2 => tabC3 0 2 0 2 0 2
  | 3 => tabC3 0 2 0 2 0 3
  | 4 => tabC3 0 2 0 2 1 0
  | 5 => tabC3 0 2 0 2 1 1
  | 6 => tabC3 0 2 0 2 1 2
  | 7 => tabC3 0 2 0 2 1 3
  | 8 => tabC3 0 2 0 2 2 0
  | 9 => tabC3 0 2 0 2 2 1
  | 10 => tabC3 0 2 0 2 2 2
  | 11 => tabC3 0 2 0 2 2 3
  | 12 => tabC3 0 2 0 2 3 0
  | 13 => tabC3 0 2 0 2 3 1
  | 14 => tabC3 0 2 0 2 3 2
  | 15 => tabC3 0 2 0 2 3 3
  | 16 => tabC3 0 2 0 3 0 0
  | 17 => tabC3 0 2 0 3 0 1
  | 18 => tabC3 0 2 0 3 0 2
  | 19 => tabC3 0 2 0 3 0 3
  | 20 => tabC3 0 2 0 3 1 0
  | 21 => tabC3 0 2 0 3 1 1
  | 22 => tabC3 0 2 0 3 1 2
  | 23 => tabC3 0 2 0 3 1 3
  | 24 => tabC3 0 2 0 3 2 0
  | 25 => tabC3 0 2 0 3 2 1
  | 26 => tabC3 0 2 0 3 2 2
  | 27 => tabC3 0 2 0 3 2 3
  | 28 => tabC3 0 2 0 3 3 0
  | 29 => tabC3 0 2 0 3 3 1
  | 30 => tabC3 0 2 0 3 3 2
  | _ => tabC3 0 2 0 3 3 3
def memRowC317 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 1 0 0 0
  | 1 => tabC3 0 2 1 0 0 1
  | 2 => tabC3 0 2 1 0 0 2
  | 3 => tabC3 0 2 1 0 0 3
  | 4 => tabC3 0 2 1 0 1 0
  | 5 => tabC3 0 2 1 0 1 1
  | 6 => tabC3 0 2 1 0 1 2
  | 7 => tabC3 0 2 1 0 1 3
  | 8 => tabC3 0 2 1 0 2 0
  | 9 => tabC3 0 2 1 0 2 1
  | 10 => tabC3 0 2 1 0 2 2
  | 11 => tabC3 0 2 1 0 2 3
  | 12 => tabC3 0 2 1 0 3 0
  | 13 => tabC3 0 2 1 0 3 1
  | 14 => tabC3 0 2 1 0 3 2
  | 15 => tabC3 0 2 1 0 3 3
  | 16 => tabC3 0 2 1 1 0 0
  | 17 => tabC3 0 2 1 1 0 1
  | 18 => tabC3 0 2 1 1 0 2
  | 19 => tabC3 0 2 1 1 0 3
  | 20 => tabC3 0 2 1 1 1 0
  | 21 => tabC3 0 2 1 1 1 1
  | 22 => tabC3 0 2 1 1 1 2
  | 23 => tabC3 0 2 1 1 1 3
  | 24 => tabC3 0 2 1 1 2 0
  | 25 => tabC3 0 2 1 1 2 1
  | 26 => tabC3 0 2 1 1 2 2
  | 27 => tabC3 0 2 1 1 2 3
  | 28 => tabC3 0 2 1 1 3 0
  | 29 => tabC3 0 2 1 1 3 1
  | 30 => tabC3 0 2 1 1 3 2
  | _ => tabC3 0 2 1 1 3 3
def memRowC318 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 1 2 0 0
  | 1 => tabC3 0 2 1 2 0 1
  | 2 => tabC3 0 2 1 2 0 2
  | 3 => tabC3 0 2 1 2 0 3
  | 4 => tabC3 0 2 1 2 1 0
  | 5 => tabC3 0 2 1 2 1 1
  | 6 => tabC3 0 2 1 2 1 2
  | 7 => tabC3 0 2 1 2 1 3
  | 8 => tabC3 0 2 1 2 2 0
  | 9 => tabC3 0 2 1 2 2 1
  | 10 => tabC3 0 2 1 2 2 2
  | 11 => tabC3 0 2 1 2 2 3
  | 12 => tabC3 0 2 1 2 3 0
  | 13 => tabC3 0 2 1 2 3 1
  | 14 => tabC3 0 2 1 2 3 2
  | 15 => tabC3 0 2 1 2 3 3
  | 16 => tabC3 0 2 1 3 0 0
  | 17 => tabC3 0 2 1 3 0 1
  | 18 => tabC3 0 2 1 3 0 2
  | 19 => tabC3 0 2 1 3 0 3
  | 20 => tabC3 0 2 1 3 1 0
  | 21 => tabC3 0 2 1 3 1 1
  | 22 => tabC3 0 2 1 3 1 2
  | 23 => tabC3 0 2 1 3 1 3
  | 24 => tabC3 0 2 1 3 2 0
  | 25 => tabC3 0 2 1 3 2 1
  | 26 => tabC3 0 2 1 3 2 2
  | 27 => tabC3 0 2 1 3 2 3
  | 28 => tabC3 0 2 1 3 3 0
  | 29 => tabC3 0 2 1 3 3 1
  | 30 => tabC3 0 2 1 3 3 2
  | _ => tabC3 0 2 1 3 3 3
def memRowC319 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 2 0 0 0
  | 1 => tabC3 0 2 2 0 0 1
  | 2 => tabC3 0 2 2 0 0 2
  | 3 => tabC3 0 2 2 0 0 3
  | 4 => tabC3 0 2 2 0 1 0
  | 5 => tabC3 0 2 2 0 1 1
  | 6 => tabC3 0 2 2 0 1 2
  | 7 => tabC3 0 2 2 0 1 3
  | 8 => tabC3 0 2 2 0 2 0
  | 9 => tabC3 0 2 2 0 2 1
  | 10 => tabC3 0 2 2 0 2 2
  | 11 => tabC3 0 2 2 0 2 3
  | 12 => tabC3 0 2 2 0 3 0
  | 13 => tabC3 0 2 2 0 3 1
  | 14 => tabC3 0 2 2 0 3 2
  | 15 => tabC3 0 2 2 0 3 3
  | 16 => tabC3 0 2 2 1 0 0
  | 17 => tabC3 0 2 2 1 0 1
  | 18 => tabC3 0 2 2 1 0 2
  | 19 => tabC3 0 2 2 1 0 3
  | 20 => tabC3 0 2 2 1 1 0
  | 21 => tabC3 0 2 2 1 1 1
  | 22 => tabC3 0 2 2 1 1 2
  | 23 => tabC3 0 2 2 1 1 3
  | 24 => tabC3 0 2 2 1 2 0
  | 25 => tabC3 0 2 2 1 2 1
  | 26 => tabC3 0 2 2 1 2 2
  | 27 => tabC3 0 2 2 1 2 3
  | 28 => tabC3 0 2 2 1 3 0
  | 29 => tabC3 0 2 2 1 3 1
  | 30 => tabC3 0 2 2 1 3 2
  | _ => tabC3 0 2 2 1 3 3
def memRowC320 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 2 2 0 0
  | 1 => tabC3 0 2 2 2 0 1
  | 2 => tabC3 0 2 2 2 0 2
  | 3 => tabC3 0 2 2 2 0 3
  | 4 => tabC3 0 2 2 2 1 0
  | 5 => tabC3 0 2 2 2 1 1
  | 6 => tabC3 0 2 2 2 1 2
  | 7 => tabC3 0 2 2 2 1 3
  | 8 => tabC3 0 2 2 2 2 0
  | 9 => tabC3 0 2 2 2 2 1
  | 10 => tabC3 0 2 2 2 2 2
  | 11 => tabC3 0 2 2 2 2 3
  | 12 => tabC3 0 2 2 2 3 0
  | 13 => tabC3 0 2 2 2 3 1
  | 14 => tabC3 0 2 2 2 3 2
  | 15 => tabC3 0 2 2 2 3 3
  | 16 => tabC3 0 2 2 3 0 0
  | 17 => tabC3 0 2 2 3 0 1
  | 18 => tabC3 0 2 2 3 0 2
  | 19 => tabC3 0 2 2 3 0 3
  | 20 => tabC3 0 2 2 3 1 0
  | 21 => tabC3 0 2 2 3 1 1
  | 22 => tabC3 0 2 2 3 1 2
  | 23 => tabC3 0 2 2 3 1 3
  | 24 => tabC3 0 2 2 3 2 0
  | 25 => tabC3 0 2 2 3 2 1
  | 26 => tabC3 0 2 2 3 2 2
  | 27 => tabC3 0 2 2 3 2 3
  | 28 => tabC3 0 2 2 3 3 0
  | 29 => tabC3 0 2 2 3 3 1
  | 30 => tabC3 0 2 2 3 3 2
  | _ => tabC3 0 2 2 3 3 3
def memRowC321 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 3 0 0 0
  | 1 => tabC3 0 2 3 0 0 1
  | 2 => tabC3 0 2 3 0 0 2
  | 3 => tabC3 0 2 3 0 0 3
  | 4 => tabC3 0 2 3 0 1 0
  | 5 => tabC3 0 2 3 0 1 1
  | 6 => tabC3 0 2 3 0 1 2
  | 7 => tabC3 0 2 3 0 1 3
  | 8 => tabC3 0 2 3 0 2 0
  | 9 => tabC3 0 2 3 0 2 1
  | 10 => tabC3 0 2 3 0 2 2
  | 11 => tabC3 0 2 3 0 2 3
  | 12 => tabC3 0 2 3 0 3 0
  | 13 => tabC3 0 2 3 0 3 1
  | 14 => tabC3 0 2 3 0 3 2
  | 15 => tabC3 0 2 3 0 3 3
  | 16 => tabC3 0 2 3 1 0 0
  | 17 => tabC3 0 2 3 1 0 1
  | 18 => tabC3 0 2 3 1 0 3
  | 19 => tabC3 0 2 3 1 1 0
  | 20 => tabC3 0 2 3 1 1 1
  | 21 => tabC3 0 2 3 1 1 2
  | 22 => tabC3 0 2 3 1 1 3
  | 23 => tabC3 0 2 3 1 2 0
  | 24 => tabC3 0 2 3 1 2 1
  | 25 => tabC3 0 2 3 1 2 2
  | 26 => tabC3 0 2 3 1 2 3
  | 27 => tabC3 0 2 3 1 3 0
  | 28 => tabC3 0 2 3 1 3 1
  | 29 => tabC3 0 2 3 1 3 2
  | 30 => tabC3 0 2 3 1 3 3
  | _ => tabC3 0 2 3 2 0 0
def memRowC322 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 2 3 2 0 1
  | 1 => tabC3 0 2 3 2 0 2
  | 2 => tabC3 0 2 3 2 0 3
  | 3 => tabC3 0 2 3 2 1 0
  | 4 => tabC3 0 2 3 2 1 1
  | 5 => tabC3 0 2 3 2 1 2
  | 6 => tabC3 0 2 3 2 1 3
  | 7 => tabC3 0 2 3 2 2 0
  | 8 => tabC3 0 2 3 2 2 1
  | 9 => tabC3 0 2 3 2 2 2
  | 10 => tabC3 0 2 3 2 2 3
  | 11 => tabC3 0 2 3 2 3 0
  | 12 => tabC3 0 2 3 2 3 1
  | 13 => tabC3 0 2 3 2 3 2
  | 14 => tabC3 0 2 3 2 3 3
  | 15 => tabC3 0 2 3 3 0 0
  | 16 => tabC3 0 2 3 3 0 1
  | 17 => tabC3 0 2 3 3 0 2
  | 18 => tabC3 0 2 3 3 0 3
  | 19 => tabC3 0 2 3 3 1 0
  | 20 => tabC3 0 2 3 3 1 1
  | 21 => tabC3 0 2 3 3 1 2
  | 22 => tabC3 0 2 3 3 1 3
  | 23 => tabC3 0 2 3 3 2 0
  | 24 => tabC3 0 2 3 3 2 1
  | 25 => tabC3 0 2 3 3 2 2
  | 26 => tabC3 0 2 3 3 2 3
  | 27 => tabC3 0 2 3 3 3 0
  | 28 => tabC3 0 2 3 3 3 1
  | 29 => tabC3 0 2 3 3 3 2
  | 30 => tabC3 0 2 3 3 3 3
  | _ => tabC3 0 3 0 0 0 0
def memRowC323 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 0 0 0 1
  | 1 => tabC3 0 3 0 0 0 2
  | 2 => tabC3 0 3 0 0 0 3
  | 3 => tabC3 0 3 0 0 1 0
  | 4 => tabC3 0 3 0 0 1 1
  | 5 => tabC3 0 3 0 0 1 2
  | 6 => tabC3 0 3 0 0 1 3
  | 7 => tabC3 0 3 0 0 2 0
  | 8 => tabC3 0 3 0 0 2 1
  | 9 => tabC3 0 3 0 0 2 2
  | 10 => tabC3 0 3 0 0 2 3
  | 11 => tabC3 0 3 0 0 3 0
  | 12 => tabC3 0 3 0 0 3 1
  | 13 => tabC3 0 3 0 0 3 2
  | 14 => tabC3 0 3 0 0 3 3
  | 15 => tabC3 0 3 0 1 0 0
  | 16 => tabC3 0 3 0 1 0 1
  | 17 => tabC3 0 3 0 1 0 2
  | 18 => tabC3 0 3 0 1 0 3
  | 19 => tabC3 0 3 0 1 1 0
  | 20 => tabC3 0 3 0 1 1 1
  | 21 => tabC3 0 3 0 1 1 2
  | 22 => tabC3 0 3 0 1 1 3
  | 23 => tabC3 0 3 0 1 2 0
  | 24 => tabC3 0 3 0 1 2 1
  | 25 => tabC3 0 3 0 1 2 2
  | 26 => tabC3 0 3 0 1 2 3
  | 27 => tabC3 0 3 0 1 3 0
  | 28 => tabC3 0 3 0 1 3 1
  | 29 => tabC3 0 3 0 1 3 2
  | 30 => tabC3 0 3 0 1 3 3
  | _ => tabC3 0 3 0 2 0 0
def memRowC324 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 0 2 0 1
  | 1 => tabC3 0 3 0 2 0 2
  | 2 => tabC3 0 3 0 2 0 3
  | 3 => tabC3 0 3 0 2 1 0
  | 4 => tabC3 0 3 0 2 1 1
  | 5 => tabC3 0 3 0 2 1 2
  | 6 => tabC3 0 3 0 2 1 3
  | 7 => tabC3 0 3 0 2 2 0
  | 8 => tabC3 0 3 0 2 2 1
  | 9 => tabC3 0 3 0 2 2 2
  | 10 => tabC3 0 3 0 2 2 3
  | 11 => tabC3 0 3 0 2 3 0
  | 12 => tabC3 0 3 0 2 3 1
  | 13 => tabC3 0 3 0 2 3 2
  | 14 => tabC3 0 3 0 2 3 3
  | 15 => tabC3 0 3 0 3 0 0
  | 16 => tabC3 0 3 0 3 0 1
  | 17 => tabC3 0 3 0 3 0 2
  | 18 => tabC3 0 3 0 3 0 3
  | 19 => tabC3 0 3 0 3 1 0
  | 20 => tabC3 0 3 0 3 1 1
  | 21 => tabC3 0 3 0 3 1 2
  | 22 => tabC3 0 3 0 3 1 3
  | 23 => tabC3 0 3 0 3 2 0
  | 24 => tabC3 0 3 0 3 2 1
  | 25 => tabC3 0 3 0 3 2 2
  | 26 => tabC3 0 3 0 3 2 3
  | 27 => tabC3 0 3 0 3 3 0
  | 28 => tabC3 0 3 0 3 3 1
  | 29 => tabC3 0 3 0 3 3 2
  | 30 => tabC3 0 3 0 3 3 3
  | _ => tabC3 0 3 1 0 0 0
def memRowC325 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 1 0 0 1
  | 1 => tabC3 0 3 1 0 0 2
  | 2 => tabC3 0 3 1 0 0 3
  | 3 => tabC3 0 3 1 0 1 0
  | 4 => tabC3 0 3 1 0 1 1
  | 5 => tabC3 0 3 1 0 1 2
  | 6 => tabC3 0 3 1 0 1 3
  | 7 => tabC3 0 3 1 0 2 0
  | 8 => tabC3 0 3 1 0 2 1
  | 9 => tabC3 0 3 1 0 2 2
  | 10 => tabC3 0 3 1 0 2 3
  | 11 => tabC3 0 3 1 0 3 0
  | 12 => tabC3 0 3 1 0 3 1
  | 13 => tabC3 0 3 1 0 3 2
  | 14 => tabC3 0 3 1 0 3 3
  | 15 => tabC3 0 3 1 1 0 0
  | 16 => tabC3 0 3 1 1 0 1
  | 17 => tabC3 0 3 1 1 0 2
  | 18 => tabC3 0 3 1 1 0 3
  | 19 => tabC3 0 3 1 1 1 0
  | 20 => tabC3 0 3 1 1 1 1
  | 21 => tabC3 0 3 1 1 1 2
  | 22 => tabC3 0 3 1 1 1 3
  | 23 => tabC3 0 3 1 1 2 0
  | 24 => tabC3 0 3 1 1 2 1
  | 25 => tabC3 0 3 1 1 2 2
  | 26 => tabC3 0 3 1 1 2 3
  | 27 => tabC3 0 3 1 1 3 0
  | 28 => tabC3 0 3 1 1 3 1
  | 29 => tabC3 0 3 1 1 3 2
  | 30 => tabC3 0 3 1 1 3 3
  | _ => tabC3 0 3 1 2 0 0
def memRowC326 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 1 2 0 1
  | 1 => tabC3 0 3 1 2 0 2
  | 2 => tabC3 0 3 1 2 0 3
  | 3 => tabC3 0 3 1 2 1 0
  | 4 => tabC3 0 3 1 2 1 1
  | 5 => tabC3 0 3 1 2 1 2
  | 6 => tabC3 0 3 1 2 1 3
  | 7 => tabC3 0 3 1 2 2 0
  | 8 => tabC3 0 3 1 2 2 1
  | 9 => tabC3 0 3 1 2 2 2
  | 10 => tabC3 0 3 1 2 2 3
  | 11 => tabC3 0 3 1 2 3 0
  | 12 => tabC3 0 3 1 2 3 1
  | 13 => tabC3 0 3 1 2 3 2
  | 14 => tabC3 0 3 1 2 3 3
  | 15 => tabC3 0 3 1 3 0 0
  | 16 => tabC3 0 3 1 3 0 1
  | 17 => tabC3 0 3 1 3 0 2
  | 18 => tabC3 0 3 1 3 0 3
  | 19 => tabC3 0 3 1 3 1 0
  | 20 => tabC3 0 3 1 3 1 1
  | 21 => tabC3 0 3 1 3 1 2
  | 22 => tabC3 0 3 1 3 1 3
  | 23 => tabC3 0 3 1 3 2 0
  | 24 => tabC3 0 3 1 3 2 1
  | 25 => tabC3 0 3 1 3 2 2
  | 26 => tabC3 0 3 1 3 2 3
  | 27 => tabC3 0 3 1 3 3 0
  | 28 => tabC3 0 3 1 3 3 1
  | 29 => tabC3 0 3 1 3 3 2
  | 30 => tabC3 0 3 1 3 3 3
  | _ => tabC3 0 3 2 0 0 0
def memRowC327 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 2 0 0 1
  | 1 => tabC3 0 3 2 0 0 2
  | 2 => tabC3 0 3 2 0 0 3
  | 3 => tabC3 0 3 2 0 1 0
  | 4 => tabC3 0 3 2 0 1 1
  | 5 => tabC3 0 3 2 0 1 2
  | 6 => tabC3 0 3 2 0 1 3
  | 7 => tabC3 0 3 2 0 2 0
  | 8 => tabC3 0 3 2 0 2 1
  | 9 => tabC3 0 3 2 0 2 2
  | 10 => tabC3 0 3 2 0 2 3
  | 11 => tabC3 0 3 2 0 3 0
  | 12 => tabC3 0 3 2 0 3 1
  | 13 => tabC3 0 3 2 0 3 2
  | 14 => tabC3 0 3 2 0 3 3
  | 15 => tabC3 0 3 2 1 0 0
  | 16 => tabC3 0 3 2 1 0 1
  | 17 => tabC3 0 3 2 1 0 2
  | 18 => tabC3 0 3 2 1 0 3
  | 19 => tabC3 0 3 2 1 1 0
  | 20 => tabC3 0 3 2 1 1 1
  | 21 => tabC3 0 3 2 1 1 2
  | 22 => tabC3 0 3 2 1 1 3
  | 23 => tabC3 0 3 2 1 2 0
  | 24 => tabC3 0 3 2 1 2 1
  | 25 => tabC3 0 3 2 1 2 2
  | 26 => tabC3 0 3 2 1 2 3
  | 27 => tabC3 0 3 2 1 3 1
  | 28 => tabC3 0 3 2 1 3 2
  | 29 => tabC3 0 3 2 1 3 3
  | 30 => tabC3 0 3 2 2 0 0
  | _ => tabC3 0 3 2 2 0 1
def memRowC328 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 2 2 0 2
  | 1 => tabC3 0 3 2 2 0 3
  | 2 => tabC3 0 3 2 2 1 0
  | 3 => tabC3 0 3 2 2 1 1
  | 4 => tabC3 0 3 2 2 1 2
  | 5 => tabC3 0 3 2 2 1 3
  | 6 => tabC3 0 3 2 2 2 0
  | 7 => tabC3 0 3 2 2 2 1
  | 8 => tabC3 0 3 2 2 2 2
  | 9 => tabC3 0 3 2 2 2 3
  | 10 => tabC3 0 3 2 2 3 0
  | 11 => tabC3 0 3 2 2 3 1
  | 12 => tabC3 0 3 2 2 3 2
  | 13 => tabC3 0 3 2 2 3 3
  | 14 => tabC3 0 3 2 3 0 0
  | 15 => tabC3 0 3 2 3 0 1
  | 16 => tabC3 0 3 2 3 0 2
  | 17 => tabC3 0 3 2 3 0 3
  | 18 => tabC3 0 3 2 3 1 0
  | 19 => tabC3 0 3 2 3 1 1
  | 20 => tabC3 0 3 2 3 1 2
  | 21 => tabC3 0 3 2 3 1 3
  | 22 => tabC3 0 3 2 3 2 0
  | 23 => tabC3 0 3 2 3 2 1
  | 24 => tabC3 0 3 2 3 2 2
  | 25 => tabC3 0 3 2 3 2 3
  | 26 => tabC3 0 3 2 3 3 0
  | 27 => tabC3 0 3 2 3 3 1
  | 28 => tabC3 0 3 2 3 3 2
  | 29 => tabC3 0 3 2 3 3 3
  | 30 => tabC3 0 3 3 0 0 0
  | _ => tabC3 0 3 3 0 0 1
def memRowC329 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 3 0 0 2
  | 1 => tabC3 0 3 3 0 0 3
  | 2 => tabC3 0 3 3 0 1 0
  | 3 => tabC3 0 3 3 0 1 1
  | 4 => tabC3 0 3 3 0 1 2
  | 5 => tabC3 0 3 3 0 1 3
  | 6 => tabC3 0 3 3 0 2 0
  | 7 => tabC3 0 3 3 0 2 1
  | 8 => tabC3 0 3 3 0 2 2
  | 9 => tabC3 0 3 3 0 2 3
  | 10 => tabC3 0 3 3 0 3 0
  | 11 => tabC3 0 3 3 0 3 1
  | 12 => tabC3 0 3 3 0 3 2
  | 13 => tabC3 0 3 3 0 3 3
  | 14 => tabC3 0 3 3 1 0 0
  | 15 => tabC3 0 3 3 1 0 1
  | 16 => tabC3 0 3 3 1 0 2
  | 17 => tabC3 0 3 3 1 0 3
  | 18 => tabC3 0 3 3 1 1 0
  | 19 => tabC3 0 3 3 1 1 1
  | 20 => tabC3 0 3 3 1 1 2
  | 21 => tabC3 0 3 3 1 1 3
  | 22 => tabC3 0 3 3 1 2 0
  | 23 => tabC3 0 3 3 1 2 1
  | 24 => tabC3 0 3 3 1 2 2
  | 25 => tabC3 0 3 3 1 2 3
  | 26 => tabC3 0 3 3 1 3 0
  | 27 => tabC3 0 3 3 1 3 1
  | 28 => tabC3 0 3 3 1 3 2
  | 29 => tabC3 0 3 3 1 3 3
  | 30 => tabC3 0 3 3 2 0 0
  | _ => tabC3 0 3 3 2 0 1
def memRowC330 : Fin 32 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabC3 0 3 3 2 0 2
  | 1 => tabC3 0 3 3 2 0 3
  | 2 => tabC3 0 3 3 2 1 0
  | 3 => tabC3 0 3 3 2 1 1
  | 4 => tabC3 0 3 3 2 1 2
  | 5 => tabC3 0 3 3 2 1 3
  | 6 => tabC3 0 3 3 2 2 0
  | 7 => tabC3 0 3 3 2 2 1
  | 8 => tabC3 0 3 3 2 2 2
  | 9 => tabC3 0 3 3 2 2 3
  | 10 => tabC3 0 3 3 2 3 0
  | 11 => tabC3 0 3 3 2 3 1
  | 12 => tabC3 0 3 3 2 3 2
  | 13 => tabC3 0 3 3 2 3 3
  | 14 => tabC3 0 3 3 3 0 0
  | 15 => tabC3 0 3 3 3 0 1
  | 16 => tabC3 0 3 3 3 0 2
  | 17 => tabC3 0 3 3 3 0 3
  | 18 => tabC3 0 3 3 3 1 0
  | 19 => tabC3 0 3 3 3 1 1
  | 20 => tabC3 0 3 3 3 1 2
  | 21 => tabC3 0 3 3 3 1 3
  | 22 => tabC3 0 3 3 3 2 0
  | 23 => tabC3 0 3 3 3 2 1
  | 24 => tabC3 0 3 3 3 2 2
  | 25 => tabC3 0 3 3 3 2 3
  | 26 => tabC3 0 3 3 3 3 0
  | 27 => tabC3 0 3 3 3 3 1
  | 28 => tabC3 0 3 3 3 3 2
  | _ => tabC3 0 3 3 3 3 3
def memC3 (i : Fin 990) : Fin 4 → Fin 4 → Fin 4 :=
  match (i.1 / 32 : Nat) with
  | 0 => memRowC30 ⟨i.1 % 32, by omega⟩
  | 1 => memRowC31 ⟨i.1 % 32, by omega⟩
  | 2 => memRowC32 ⟨i.1 % 32, by omega⟩
  | 3 => memRowC33 ⟨i.1 % 32, by omega⟩
  | 4 => memRowC34 ⟨i.1 % 32, by omega⟩
  | 5 => memRowC35 ⟨i.1 % 32, by omega⟩
  | 6 => memRowC36 ⟨i.1 % 32, by omega⟩
  | 7 => memRowC37 ⟨i.1 % 32, by omega⟩
  | 8 => memRowC38 ⟨i.1 % 32, by omega⟩
  | 9 => memRowC39 ⟨i.1 % 32, by omega⟩
  | 10 => memRowC310 ⟨i.1 % 32, by omega⟩
  | 11 => memRowC311 ⟨i.1 % 32, by omega⟩
  | 12 => memRowC312 ⟨i.1 % 32, by omega⟩
  | 13 => memRowC313 ⟨i.1 % 32, by omega⟩
  | 14 => memRowC314 ⟨i.1 % 32, by omega⟩
  | 15 => memRowC315 ⟨i.1 % 32, by omega⟩
  | 16 => memRowC316 ⟨i.1 % 32, by omega⟩
  | 17 => memRowC317 ⟨i.1 % 32, by omega⟩
  | 18 => memRowC318 ⟨i.1 % 32, by omega⟩
  | 19 => memRowC319 ⟨i.1 % 32, by omega⟩
  | 20 => memRowC320 ⟨i.1 % 32, by omega⟩
  | 21 => memRowC321 ⟨i.1 % 32, by omega⟩
  | 22 => memRowC322 ⟨i.1 % 32, by omega⟩
  | 23 => memRowC323 ⟨i.1 % 32, by omega⟩
  | 24 => memRowC324 ⟨i.1 % 32, by omega⟩
  | 25 => memRowC325 ⟨i.1 % 32, by omega⟩
  | 26 => memRowC326 ⟨i.1 % 32, by omega⟩
  | 27 => memRowC327 ⟨i.1 % 32, by omega⟩
  | 28 => memRowC328 ⟨i.1 % 32, by omega⟩
  | 29 => memRowC329 ⟨i.1 % 32, by omega⟩
  | _ => memRowC330 ⟨i.1 % 32, by omega⟩

/-- Which of the `990` members a given invariant tuple is, so that `mem_of_isExactC3` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrC3 : Array Nat := #[
  0, 0, 1, 2, 3, 0, 4, 5, 6, 7, 8, 0, 9, 10, 0, 11, 0, 12, 13, 14, 15, 0, 16, 17, 18, 19, 20, 0,
  21, 22, 0, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 0, 56, 57, 58, 59, 0, 60, 61, 62, 63, 64, 0,
  65, 66, 0, 67, 0, 68, 69, 70, 71, 0, 72, 73, 74, 75, 76, 0, 77, 78, 0, 79, 80, 81, 82, 83, 84,
  85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
  107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
  126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
  145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
  164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182,
  183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
  202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220,
  221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
  0, 240, 241, 242, 243, 0, 244, 245, 246, 247, 248, 0, 249, 250, 0, 251, 0, 252, 253, 254, 255,
  0, 256, 257, 258, 259, 260, 0, 261, 262, 0, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272,
  273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291,
  292, 293, 294, 295, 0, 296, 297, 298, 299, 0, 300, 301, 302, 303, 304, 0, 305, 306, 0, 307, 0,
  308, 309, 310, 311, 0, 312, 313, 314, 315, 316, 0, 317, 318, 0, 319, 320, 321, 322, 323, 324,
  325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343,
  344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362,
  363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381,
  382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400,
  401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419,
  420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438,
  439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457,
  458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476,
  477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495,
  496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514,
  515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533,
  534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552,
  553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571,
  572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590,
  591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609,
  610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628,
  629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647,
  648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666,
  667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685,
  686, 687, 688, 689, 0, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703,
  704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722,
  723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741,
  742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760,
  761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779,
  780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798,
  799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817,
  818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836,
  837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855,
  856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874,
  875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 0, 891, 892,
  893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911,
  912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930,
  931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949,
  950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968,
  969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987,
  988, 989]

/-- The arguments as one mixed-radix index, which is how `rankArrC3` is addressed. -/
def encTC3 (a : Fin 1) (b c d e f : Fin 4) : Nat :=
  a.1 * 1024 +
    b.1 * 256 +
    c.1 * 64 +
    d.1 * 16 +
    e.1 * 4 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankC3 (a : Fin 1) (b c d e f : Fin 4) : Fin 990 :=
  ⟨min (rankArrC3.getD (encTC3 a b c d e f) 0) 989, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactC3 (i : Fin 990) : Magma (Fin 4) := Magma.mk (memC3 i)

theorem exactC3_isEndo (i : Fin 990) (j : Fin 3) : (exactC3 i).IsEndo ⇑(eEC3 j) := by
  simp only [eEC3, coe_permOf]; revert i j; native_decide

theorem exactC3_not_isEndo (i : Fin 990) (j : Fin 2) : ¬ (exactC3 i).IsEndo ⇑(eXC3 j) := by
  simp only [eXC3, coe_permOf]; revert i j; native_decide

/-- `rankC3` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memC3` for the index would be a comparison per tuple and
member. -/
theorem mem_rankC3 (a : Fin 1) (b c d e f : Fin 4)
    (h : Magma.isExact (tabC3 a b c d e f) permEC3 permXC3 = true) :
    memC3 (rankC3 a b c d e f) = tabC3 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `990`
listed members. -/
theorem mem_of_isExactC3 (a : Fin 1) (b c d e f : Fin 4)
    (h : Magma.isExact (tabC3 a b c d e f) permEC3 permXC3 = true) :
    ∃ i, memC3 i = tabC3 a b c d e f :=
  ⟨_, mem_rankC3 a b c d e f h⟩

/-- A magma on `Fin 4` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactC3`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactC3` turns that into a member index. -/
theorem exists_exactC3 {M : Magma (Fin 4)} (hE : ∀ i, M.IsEndo ⇑(eEC3 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXC3 i)) : ∃ i, exactC3 i = M := by
  simp only [eEC3, coe_permOf] at hE
  simp only [eXC3, coe_permOf] at hX
  have hop : M.op = Magma.transport permEC3 trC3 (fun i ↦ M.op (repC3 i).1 (repC3 i).2) :=
    Magma.op_eq_transport (rep := repC3) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEC3) (idx := stabIdxC30) (a := (repC3 0).1) (b := (repC3 0).2)
    (val := valC30) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEC3) (idx := stabIdxC31) (a := (repC3 1).1) (b := (repC3 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEC3) (idx := stabIdxC32) (a := (repC3 2).1) (b := (repC3 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEC3) (idx := stabIdxC33) (a := (repC3 3).1) (b := (repC3 3).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEC3) (idx := stabIdxC34) (a := (repC3 4).1) (b := (repC3 4).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permEC3) (idx := stabIdxC35) (a := (repC3 5).1) (b := (repC3 5).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decC3 a b c d e f = fun i ↦ M.op (repC3 i).1 (repC3 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabC3 a b c d e f = M.op := by
    rw [tabC3_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabC3 a b c d e f) permEC3 permXC3 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactC3 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose automorphism
group is exactly the order-`3` group of `Magma.permEC3`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactC3 {L L' : Law.NatMagmaLaw} {i : Fin 990}
    (hsrc : @satisfies _ (Fin 4) (Magma.exactC3 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.exactC3 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactC3 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactC3
    (fun k ↦ (Magma.exactC3_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactC3_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
