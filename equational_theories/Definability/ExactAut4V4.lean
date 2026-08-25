import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `V4` on `Fin 4`

One class of `Definability/ExactAut4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`4` group `⟨(0 3)(1 2), (1 2)⟩` -/

/-- The `4` elements of the group: `()`, `(1 2)`, `(0 3)`, `(0 3)(1 2)`. -/
def pEV40 : Fin 4 → Fin 4 := id
def pEV41 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pEV42 : Fin 4 → Fin 4 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0
def pEV43 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permEV4 : Fin 4 → Fin 4 → Fin 4
  | 0 => pEV40
  | 1 => pEV41
  | 2 => pEV42
  | 3 => pEV43

def permEinvV4 : Fin 4 → Fin 4 → Fin 4
  | 0 => pEV40
  | 1 => pEV41
  | 2 => pEV42
  | 3 => pEV43

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEV4 (i : Fin 4) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permEV4 i) (permEinvV4 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 2)(1 3)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXV40 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pXV40inv : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1

def permXV4 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXV40

def permXinvV4 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXV40inv

def eXV4 (i : Fin 1) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permXV4 i) (permXinvV4 i) (by revert i; decide)

/-- One representative per orbit of the group on the `16` cells; there are `6`, so an invariant
operation is `6` values. -/
def repV4 : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trV4 : Fin 4 → Fin 4 → Fin 6 × Fin 4
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 1, 0 => (3, 0)
  | 1, 1 => (4, 0)
  | 1, 2 => (5, 0)
  | 1, 3 => (3, 2)
  | 2, 0 => (3, 1)
  | 2, 1 => (5, 1)
  | 2, 2 => (4, 1)
  | 2, 3 => (3, 3)
  | 3, 0 => (2, 2)
  | 3, 1 => (1, 2)
  | 3, 2 => (1, 3)
  | 3, 3 => (0, 2)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxV40 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1
def valV40 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxV41 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxV42 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1
def valV42 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxV43 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxV44 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 2
def valV44 : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxV45 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 2
def valV45 : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- The `6` orbit values named by the family's arguments. -/
def decV4 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 6 → Fin 4
  | 0 => valV40 a
  | 1 => b
  | 2 => valV42 c
  | 3 => d
  | 4 => valV44 e
  | 5 => valV45 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabV4_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabV4 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => valV40 a
  | 0, 1 => b
  | 0, 2 => pEV41 b
  | 0, 3 => valV42 c
  | 1, 0 => d
  | 1, 1 => valV44 e
  | 1, 2 => valV45 f
  | 1, 3 => pEV42 d
  | 2, 0 => pEV41 d
  | 2, 1 => pEV41 (valV45 f)
  | 2, 2 => pEV41 (valV44 e)
  | 2, 3 => pEV43 d
  | 3, 0 => pEV42 (valV42 c)
  | 3, 1 => pEV42 b
  | 3, 2 => pEV43 b
  | 3, 3 => pEV42 (valV40 a)

theorem tabV4_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) :
    tabV4 a b c d e f = Magma.transport permEV4 trV4 (decV4 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `240` magmas on `Fin 4` whose automorphism group is exactly this group, listed under one
index. Of the `256` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowV40 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 0 0 0 0 0
  | 1 => tabV4 0 0 0 0 0 1
  | 2 => tabV4 0 0 0 0 1 0
  | 3 => tabV4 0 0 0 0 1 1
  | 4 => tabV4 0 0 0 1 0 1
  | 5 => tabV4 0 0 0 1 1 0
  | 6 => tabV4 0 0 0 1 1 1
  | 7 => tabV4 0 0 0 2 0 0
  | 8 => tabV4 0 0 0 2 0 1
  | 9 => tabV4 0 0 0 2 1 0
  | 10 => tabV4 0 0 0 2 1 1
  | 11 => tabV4 0 0 0 3 0 0
  | 12 => tabV4 0 0 0 3 0 1
  | 13 => tabV4 0 0 0 3 1 0
  | 14 => tabV4 0 0 0 3 1 1
  | _ => tabV4 0 0 1 0 0 0
def memRowV41 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 0 1 0 0 1
  | 1 => tabV4 0 0 1 0 1 0
  | 2 => tabV4 0 0 1 0 1 1
  | 3 => tabV4 0 0 1 1 0 0
  | 4 => tabV4 0 0 1 1 1 0
  | 5 => tabV4 0 0 1 1 1 1
  | 6 => tabV4 0 0 1 2 0 0
  | 7 => tabV4 0 0 1 2 0 1
  | 8 => tabV4 0 0 1 2 1 0
  | 9 => tabV4 0 0 1 2 1 1
  | 10 => tabV4 0 0 1 3 0 0
  | 11 => tabV4 0 0 1 3 0 1
  | 12 => tabV4 0 0 1 3 1 0
  | 13 => tabV4 0 0 1 3 1 1
  | 14 => tabV4 0 1 0 0 0 1
  | _ => tabV4 0 1 0 0 1 0
def memRowV42 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 1 0 0 1 1
  | 1 => tabV4 0 1 0 1 0 0
  | 2 => tabV4 0 1 0 1 0 1
  | 3 => tabV4 0 1 0 1 1 0
  | 4 => tabV4 0 1 0 1 1 1
  | 5 => tabV4 0 1 0 2 0 0
  | 6 => tabV4 0 1 0 2 0 1
  | 7 => tabV4 0 1 0 2 1 0
  | 8 => tabV4 0 1 0 2 1 1
  | 9 => tabV4 0 1 0 3 0 0
  | 10 => tabV4 0 1 0 3 0 1
  | 11 => tabV4 0 1 0 3 1 0
  | 12 => tabV4 0 1 0 3 1 1
  | 13 => tabV4 0 1 1 0 0 0
  | 14 => tabV4 0 1 1 0 1 0
  | _ => tabV4 0 1 1 0 1 1
def memRowV43 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 1 1 1 0 0
  | 1 => tabV4 0 1 1 1 0 1
  | 2 => tabV4 0 1 1 1 1 0
  | 3 => tabV4 0 1 1 1 1 1
  | 4 => tabV4 0 1 1 2 0 0
  | 5 => tabV4 0 1 1 2 0 1
  | 6 => tabV4 0 1 1 2 1 0
  | 7 => tabV4 0 1 1 2 1 1
  | 8 => tabV4 0 1 1 3 0 0
  | 9 => tabV4 0 1 1 3 0 1
  | 10 => tabV4 0 1 1 3 1 0
  | 11 => tabV4 0 1 1 3 1 1
  | 12 => tabV4 0 2 0 0 0 0
  | 13 => tabV4 0 2 0 0 0 1
  | 14 => tabV4 0 2 0 0 1 0
  | _ => tabV4 0 2 0 0 1 1
def memRowV44 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 2 0 1 0 0
  | 1 => tabV4 0 2 0 1 0 1
  | 2 => tabV4 0 2 0 1 1 0
  | 3 => tabV4 0 2 0 1 1 1
  | 4 => tabV4 0 2 0 2 0 0
  | 5 => tabV4 0 2 0 2 0 1
  | 6 => tabV4 0 2 0 2 1 0
  | 7 => tabV4 0 2 0 2 1 1
  | 8 => tabV4 0 2 0 3 0 1
  | 9 => tabV4 0 2 0 3 1 0
  | 10 => tabV4 0 2 0 3 1 1
  | 11 => tabV4 0 2 1 0 0 0
  | 12 => tabV4 0 2 1 0 0 1
  | 13 => tabV4 0 2 1 0 1 0
  | 14 => tabV4 0 2 1 0 1 1
  | _ => tabV4 0 2 1 1 0 0
def memRowV45 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 2 1 1 0 1
  | 1 => tabV4 0 2 1 1 1 0
  | 2 => tabV4 0 2 1 1 1 1
  | 3 => tabV4 0 2 1 2 0 0
  | 4 => tabV4 0 2 1 2 0 1
  | 5 => tabV4 0 2 1 2 1 0
  | 6 => tabV4 0 2 1 2 1 1
  | 7 => tabV4 0 2 1 3 0 0
  | 8 => tabV4 0 2 1 3 1 0
  | 9 => tabV4 0 2 1 3 1 1
  | 10 => tabV4 0 3 0 0 0 0
  | 11 => tabV4 0 3 0 0 0 1
  | 12 => tabV4 0 3 0 0 1 0
  | 13 => tabV4 0 3 0 0 1 1
  | 14 => tabV4 0 3 0 1 0 0
  | _ => tabV4 0 3 0 1 0 1
def memRowV46 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 3 0 1 1 0
  | 1 => tabV4 0 3 0 1 1 1
  | 2 => tabV4 0 3 0 2 0 1
  | 3 => tabV4 0 3 0 2 1 0
  | 4 => tabV4 0 3 0 2 1 1
  | 5 => tabV4 0 3 0 3 0 0
  | 6 => tabV4 0 3 0 3 0 1
  | 7 => tabV4 0 3 0 3 1 0
  | 8 => tabV4 0 3 0 3 1 1
  | 9 => tabV4 0 3 1 0 0 0
  | 10 => tabV4 0 3 1 0 0 1
  | 11 => tabV4 0 3 1 0 1 0
  | 12 => tabV4 0 3 1 0 1 1
  | 13 => tabV4 0 3 1 1 0 0
  | 14 => tabV4 0 3 1 1 0 1
  | _ => tabV4 0 3 1 1 1 0
def memRowV47 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 0 3 1 1 1 1
  | 1 => tabV4 0 3 1 2 0 0
  | 2 => tabV4 0 3 1 2 1 0
  | 3 => tabV4 0 3 1 2 1 1
  | 4 => tabV4 0 3 1 3 0 0
  | 5 => tabV4 0 3 1 3 0 1
  | 6 => tabV4 0 3 1 3 1 0
  | 7 => tabV4 0 3 1 3 1 1
  | 8 => tabV4 1 0 0 0 0 0
  | 9 => tabV4 1 0 0 0 0 1
  | 10 => tabV4 1 0 0 0 1 0
  | 11 => tabV4 1 0 0 0 1 1
  | 12 => tabV4 1 0 0 1 0 0
  | 13 => tabV4 1 0 0 1 0 1
  | 14 => tabV4 1 0 0 1 1 1
  | _ => tabV4 1 0 0 2 0 0
def memRowV48 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 0 0 2 0 1
  | 1 => tabV4 1 0 0 2 1 0
  | 2 => tabV4 1 0 0 2 1 1
  | 3 => tabV4 1 0 0 3 0 0
  | 4 => tabV4 1 0 0 3 0 1
  | 5 => tabV4 1 0 0 3 1 0
  | 6 => tabV4 1 0 0 3 1 1
  | 7 => tabV4 1 0 1 0 0 0
  | 8 => tabV4 1 0 1 0 0 1
  | 9 => tabV4 1 0 1 0 1 0
  | 10 => tabV4 1 0 1 0 1 1
  | 11 => tabV4 1 0 1 1 0 0
  | 12 => tabV4 1 0 1 1 0 1
  | 13 => tabV4 1 0 1 1 1 0
  | 14 => tabV4 1 0 1 2 0 0
  | _ => tabV4 1 0 1 2 0 1
def memRowV49 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 0 1 2 1 0
  | 1 => tabV4 1 0 1 2 1 1
  | 2 => tabV4 1 0 1 3 0 0
  | 3 => tabV4 1 0 1 3 0 1
  | 4 => tabV4 1 0 1 3 1 0
  | 5 => tabV4 1 0 1 3 1 1
  | 6 => tabV4 1 1 0 0 0 0
  | 7 => tabV4 1 1 0 0 0 1
  | 8 => tabV4 1 1 0 0 1 1
  | 9 => tabV4 1 1 0 1 0 0
  | 10 => tabV4 1 1 0 1 0 1
  | 11 => tabV4 1 1 0 1 1 0
  | 12 => tabV4 1 1 0 1 1 1
  | 13 => tabV4 1 1 0 2 0 0
  | 14 => tabV4 1 1 0 2 0 1
  | _ => tabV4 1 1 0 2 1 0
def memRowV410 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 1 0 2 1 1
  | 1 => tabV4 1 1 0 3 0 0
  | 2 => tabV4 1 1 0 3 0 1
  | 3 => tabV4 1 1 0 3 1 0
  | 4 => tabV4 1 1 0 3 1 1
  | 5 => tabV4 1 1 1 0 0 0
  | 6 => tabV4 1 1 1 0 0 1
  | 7 => tabV4 1 1 1 0 1 0
  | 8 => tabV4 1 1 1 1 0 0
  | 9 => tabV4 1 1 1 1 0 1
  | 10 => tabV4 1 1 1 1 1 0
  | 11 => tabV4 1 1 1 1 1 1
  | 12 => tabV4 1 1 1 2 0 0
  | 13 => tabV4 1 1 1 2 0 1
  | 14 => tabV4 1 1 1 2 1 0
  | _ => tabV4 1 1 1 2 1 1
def memRowV411 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 1 1 3 0 0
  | 1 => tabV4 1 1 1 3 0 1
  | 2 => tabV4 1 1 1 3 1 0
  | 3 => tabV4 1 1 1 3 1 1
  | 4 => tabV4 1 2 0 0 0 0
  | 5 => tabV4 1 2 0 0 0 1
  | 6 => tabV4 1 2 0 0 1 0
  | 7 => tabV4 1 2 0 0 1 1
  | 8 => tabV4 1 2 0 1 0 0
  | 9 => tabV4 1 2 0 1 0 1
  | 10 => tabV4 1 2 0 1 1 0
  | 11 => tabV4 1 2 0 1 1 1
  | 12 => tabV4 1 2 0 2 0 0
  | 13 => tabV4 1 2 0 2 0 1
  | 14 => tabV4 1 2 0 2 1 0
  | _ => tabV4 1 2 0 2 1 1
def memRowV412 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 2 0 3 0 0
  | 1 => tabV4 1 2 0 3 0 1
  | 2 => tabV4 1 2 0 3 1 1
  | 3 => tabV4 1 2 1 0 0 0
  | 4 => tabV4 1 2 1 0 0 1
  | 5 => tabV4 1 2 1 0 1 0
  | 6 => tabV4 1 2 1 0 1 1
  | 7 => tabV4 1 2 1 1 0 0
  | 8 => tabV4 1 2 1 1 0 1
  | 9 => tabV4 1 2 1 1 1 0
  | 10 => tabV4 1 2 1 1 1 1
  | 11 => tabV4 1 2 1 2 0 0
  | 12 => tabV4 1 2 1 2 0 1
  | 13 => tabV4 1 2 1 2 1 0
  | 14 => tabV4 1 2 1 2 1 1
  | _ => tabV4 1 2 1 3 0 0
def memRowV413 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 2 1 3 0 1
  | 1 => tabV4 1 2 1 3 1 0
  | 2 => tabV4 1 3 0 0 0 0
  | 3 => tabV4 1 3 0 0 0 1
  | 4 => tabV4 1 3 0 0 1 0
  | 5 => tabV4 1 3 0 0 1 1
  | 6 => tabV4 1 3 0 1 0 0
  | 7 => tabV4 1 3 0 1 0 1
  | 8 => tabV4 1 3 0 1 1 0
  | 9 => tabV4 1 3 0 1 1 1
  | 10 => tabV4 1 3 0 2 0 0
  | 11 => tabV4 1 3 0 2 0 1
  | 12 => tabV4 1 3 0 2 1 1
  | 13 => tabV4 1 3 0 3 0 0
  | 14 => tabV4 1 3 0 3 0 1
  | _ => tabV4 1 3 0 3 1 0
def memRowV414 : Fin 16 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabV4 1 3 0 3 1 1
  | 1 => tabV4 1 3 1 0 0 0
  | 2 => tabV4 1 3 1 0 0 1
  | 3 => tabV4 1 3 1 0 1 0
  | 4 => tabV4 1 3 1 0 1 1
  | 5 => tabV4 1 3 1 1 0 0
  | 6 => tabV4 1 3 1 1 0 1
  | 7 => tabV4 1 3 1 1 1 0
  | 8 => tabV4 1 3 1 1 1 1
  | 9 => tabV4 1 3 1 2 0 0
  | 10 => tabV4 1 3 1 2 0 1
  | 11 => tabV4 1 3 1 2 1 0
  | 12 => tabV4 1 3 1 3 0 0
  | 13 => tabV4 1 3 1 3 0 1
  | 14 => tabV4 1 3 1 3 1 0
  | _ => tabV4 1 3 1 3 1 1
def memV4 (i : Fin 240) : Fin 4 → Fin 4 → Fin 4 :=
  match (i.1 / 16 : Nat) with
  | 0 => memRowV40 ⟨i.1 % 16, by omega⟩
  | 1 => memRowV41 ⟨i.1 % 16, by omega⟩
  | 2 => memRowV42 ⟨i.1 % 16, by omega⟩
  | 3 => memRowV43 ⟨i.1 % 16, by omega⟩
  | 4 => memRowV44 ⟨i.1 % 16, by omega⟩
  | 5 => memRowV45 ⟨i.1 % 16, by omega⟩
  | 6 => memRowV46 ⟨i.1 % 16, by omega⟩
  | 7 => memRowV47 ⟨i.1 % 16, by omega⟩
  | 8 => memRowV48 ⟨i.1 % 16, by omega⟩
  | 9 => memRowV49 ⟨i.1 % 16, by omega⟩
  | 10 => memRowV410 ⟨i.1 % 16, by omega⟩
  | 11 => memRowV411 ⟨i.1 % 16, by omega⟩
  | 12 => memRowV412 ⟨i.1 % 16, by omega⟩
  | 13 => memRowV413 ⟨i.1 % 16, by omega⟩
  | _ => memRowV414 ⟨i.1 % 16, by omega⟩

/-- Which of the `240` members a given invariant tuple is, so that `mem_of_isExactV4` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrV4 : Array Nat := #[
  0, 1, 2, 3, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 0, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 0, 46,
  47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
  71, 0, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 0, 88, 89, 90, 91, 92,
  93, 94, 95, 96, 97, 0, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112,
  113, 0, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 0, 126, 127, 128, 129, 130,
  131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 0, 142, 143, 144, 145, 146, 147, 148,
  149, 150, 151, 0, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166,
  167, 0, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
  185, 186, 187, 188, 189, 190, 191, 192, 193, 0, 194, 195, 196, 197, 198, 199, 200, 201, 202,
  203, 204, 205, 206, 207, 208, 209, 0, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 0, 220,
  221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 0, 236, 237, 238, 239]

/-- The arguments as one mixed-radix index, which is how `rankArrV4` is addressed. -/
def encTV4 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Nat :=
  a.1 * 128 +
    b.1 * 32 +
    c.1 * 16 +
    d.1 * 4 +
    e.1 * 2 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankV4 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 240 :=
  ⟨min (rankArrV4.getD (encTV4 a b c d e f) 0) 239, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactV4 (i : Fin 240) : Magma (Fin 4) := Magma.mk (memV4 i)

theorem exactV4_isEndo (i : Fin 240) (j : Fin 4) : (exactV4 i).IsEndo ⇑(eEV4 j) := by
  simp only [eEV4, coe_permOf]; revert i j; native_decide

theorem exactV4_not_isEndo (i : Fin 240) (j : Fin 1) : ¬ (exactV4 i).IsEndo ⇑(eXV4 j) := by
  simp only [eXV4, coe_permOf]; revert i j; native_decide

/-- `rankV4` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memV4` for the index would be a comparison per tuple and
member. -/
theorem mem_rankV4 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2)
    (h : Magma.isExact (tabV4 a b c d e f) permEV4 permXV4 = true) :
    memV4 (rankV4 a b c d e f) = tabV4 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `240`
listed members. -/
theorem mem_of_isExactV4 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2)
    (h : Magma.isExact (tabV4 a b c d e f) permEV4 permXV4 = true) :
    ∃ i, memV4 i = tabV4 a b c d e f :=
  ⟨_, mem_rankV4 a b c d e f h⟩

/-- A magma on `Fin 4` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactV4`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactV4` turns that into a member index. -/
theorem exists_exactV4 {M : Magma (Fin 4)} (hE : ∀ i, M.IsEndo ⇑(eEV4 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXV4 i)) : ∃ i, exactV4 i = M := by
  simp only [eEV4, coe_permOf] at hE
  simp only [eXV4, coe_permOf] at hX
  have hop : M.op = Magma.transport permEV4 trV4 (fun i ↦ M.op (repV4 i).1 (repV4 i).2) :=
    Magma.op_eq_transport (rep := repV4) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEV4) (idx := stabIdxV40) (a := (repV4 0).1) (b := (repV4 0).2)
    (val := valV40) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEV4) (idx := stabIdxV41) (a := (repV4 1).1) (b := (repV4 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEV4) (idx := stabIdxV42) (a := (repV4 2).1) (b := (repV4 2).2)
    (val := valV42) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEV4) (idx := stabIdxV43) (a := (repV4 3).1) (b := (repV4 3).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEV4) (idx := stabIdxV44) (a := (repV4 4).1) (b := (repV4 4).2)
    (val := valV44) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permEV4) (idx := stabIdxV45) (a := (repV4 5).1) (b := (repV4 5).2)
    (val := valV45) hE (by decide) (by decide)
  have hdec : decV4 a b c d e f = fun i ↦ M.op (repV4 i).1 (repV4 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabV4 a b c d e f = M.op := by
    rw [tabV4_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabV4 a b c d e f) permEV4 permXV4 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactV4 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose automorphism
group is exactly the order-`4` group of `Magma.permEV4`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactV4 {L L' : Law.NatMagmaLaw} {i : Fin 240}
    (hsrc : @satisfies _ (Fin 4) (Magma.exactV4 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.exactV4 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactV4 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactV4
    (fun k ↦ (Magma.exactV4_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactV4_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
