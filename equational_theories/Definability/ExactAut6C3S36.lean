import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `C3S36` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`18` group `⟨(0 1)(2 3)(4 5), (0 1 3 2 5 4)⟩` -/

/-- The `18` elements of the group: `()`, `(1 2 4)`, `(1 4 2)`, `(0 1)(2 3)(4 5)`, `(0 1 3 2 5 4)`,
`(0 1 5 4 3 2)`, `(0 2 3 4 5 1)`, `(0 2 5 1 3 4)`, `(0 2)(1 5)(3 4)`, `(0 3 5)`, `(0 3 5)(1 2 4)`,
`(0 3 5)(1 4 2)`, `(0 4 5 2 3 1)`, `(0 4)(1 3)(2 5)`, `(0 4 3 1 5 2)`, `(0 5 3)`, `(0 5 3)(1 2 4)`,
`(0 5 3)(1 4 2)`. -/
def pEC3S360 : Fin 6 → Fin 6 := id
def pEC3S361 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5
def pEC3S362 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5
def pEC3S363 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pEC3S364 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 4
def pEC3S365 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 4
def pEC3S366 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 1
def pEC3S367 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 1
def pEC3S368 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1
def pEC3S369 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 0
def pEC3S3610 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 0
def pEC3S3611 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 0
def pEC3S3612 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 2
def pEC3S3613 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 0 | 5 => 2
def pEC3S3614 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 2
def pEC3S3615 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 3
def pEC3S3616 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 3
def pEC3S3617 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 3

def permEC3S36 : Fin 18 → Fin 6 → Fin 6
  | 0 => pEC3S360
  | 1 => pEC3S361
  | 2 => pEC3S362
  | 3 => pEC3S363
  | 4 => pEC3S364
  | 5 => pEC3S365
  | 6 => pEC3S366
  | 7 => pEC3S367
  | 8 => pEC3S368
  | 9 => pEC3S369
  | 10 => pEC3S3610
  | 11 => pEC3S3611
  | 12 => pEC3S3612
  | 13 => pEC3S3613
  | 14 => pEC3S3614
  | 15 => pEC3S3615
  | 16 => pEC3S3616
  | _ => pEC3S3617

def permEinvC3S36 : Fin 18 → Fin 6 → Fin 6
  | 0 => pEC3S360
  | 1 => pEC3S362
  | 2 => pEC3S361
  | 3 => pEC3S363
  | 4 => pEC3S3612
  | 5 => pEC3S366
  | 6 => pEC3S365
  | 7 => pEC3S3614
  | 8 => pEC3S368
  | 9 => pEC3S3615
  | 10 => pEC3S3617
  | 11 => pEC3S3616
  | 12 => pEC3S364
  | 13 => pEC3S3613
  | 14 => pEC3S367
  | 15 => pEC3S369
  | 16 => pEC3S3611
  | _ => pEC3S3610

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEC3S36 (i : Fin 18) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permEC3S36 i) (permEinvC3S36 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 1)(2 5)(3 4)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXC3S360 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2
def pXC3S360inv : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2

def permXC3S36 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXC3S360

def permXinvC3S36 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXC3S360inv

def eXC3S36 (i : Fin 1) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXC3S36 i) (permXinvC3S36 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def repC3S36 : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trC3S36 : Fin 6 → Fin 6 → Fin 4 × Fin 18
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (1, 2)
  | 0, 5 => (3, 0)
  | 1, 0 => (1, 3)
  | 1, 1 => (0, 3)
  | 1, 2 => (2, 3)
  | 1, 3 => (1, 4)
  | 1, 4 => (3, 3)
  | 1, 5 => (1, 5)
  | 2, 0 => (1, 6)
  | 2, 1 => (3, 6)
  | 2, 2 => (0, 6)
  | 2, 3 => (1, 7)
  | 2, 4 => (2, 6)
  | 2, 5 => (1, 8)
  | 3, 0 => (3, 9)
  | 3, 1 => (1, 9)
  | 3, 2 => (1, 10)
  | 3, 3 => (0, 9)
  | 3, 4 => (1, 11)
  | 3, 5 => (2, 9)
  | 4, 0 => (1, 12)
  | 4, 1 => (2, 12)
  | 4, 2 => (3, 12)
  | 4, 3 => (1, 13)
  | 4, 4 => (0, 12)
  | 4, 5 => (1, 14)
  | 5, 0 => (2, 15)
  | 5, 1 => (1, 15)
  | 5, 2 => (1, 16)
  | 5, 3 => (3, 15)
  | 5, 4 => (1, 17)
  | 5, 5 => (0, 15)

/-- The `3` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxC3S360 : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valC3S360 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxC3S361 : Fin 1 → Fin 18
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxC3S362 : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valC3S362 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxC3S363 : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valC3S363 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The `4` orbit values named by the family's arguments. -/
def decC3S36 (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Fin 4 → Fin 6
  | 0 => valC3S360 a
  | 1 => b
  | 2 => valC3S362 c
  | 3 => valC3S363 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabC3S36_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabC3S36 (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valC3S360 a
  | 0, 1 => b
  | 0, 2 => pEC3S361 b
  | 0, 3 => valC3S362 c
  | 0, 4 => pEC3S362 b
  | 0, 5 => valC3S363 d
  | 1, 0 => pEC3S363 b
  | 1, 1 => pEC3S363 (valC3S360 a)
  | 1, 2 => pEC3S363 (valC3S362 c)
  | 1, 3 => pEC3S364 b
  | 1, 4 => pEC3S363 (valC3S363 d)
  | 1, 5 => pEC3S365 b
  | 2, 0 => pEC3S366 b
  | 2, 1 => pEC3S366 (valC3S363 d)
  | 2, 2 => pEC3S366 (valC3S360 a)
  | 2, 3 => pEC3S367 b
  | 2, 4 => pEC3S366 (valC3S362 c)
  | 2, 5 => pEC3S368 b
  | 3, 0 => pEC3S369 (valC3S363 d)
  | 3, 1 => pEC3S369 b
  | 3, 2 => pEC3S3610 b
  | 3, 3 => pEC3S369 (valC3S360 a)
  | 3, 4 => pEC3S3611 b
  | 3, 5 => pEC3S369 (valC3S362 c)
  | 4, 0 => pEC3S3612 b
  | 4, 1 => pEC3S3612 (valC3S362 c)
  | 4, 2 => pEC3S3612 (valC3S363 d)
  | 4, 3 => pEC3S3613 b
  | 4, 4 => pEC3S3612 (valC3S360 a)
  | 4, 5 => pEC3S3614 b
  | 5, 0 => pEC3S3615 (valC3S362 c)
  | 5, 1 => pEC3S3615 b
  | 5, 2 => pEC3S3616 b
  | 5, 3 => pEC3S3615 (valC3S363 d)
  | 5, 4 => pEC3S3617 b
  | 5, 5 => pEC3S3615 (valC3S360 a)

theorem tabC3S36_eq_transport (a : Fin 3) (b : Fin 6) (c d : Fin 3) :
    tabC3S36 a b c d = Magma.transport permEC3S36 trC3S36 (decC3S36 a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `156` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `162` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowC3S360 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 0 0 0 1
  | 1 => tabC3S36 0 0 0 2
  | 2 => tabC3S36 0 0 1 0
  | 3 => tabC3S36 0 0 1 1
  | 4 => tabC3S36 0 0 2 0
  | 5 => tabC3S36 0 0 2 2
  | 6 => tabC3S36 0 1 0 1
  | 7 => tabC3S36 0 1 0 2
  | 8 => tabC3S36 0 1 1 0
  | 9 => tabC3S36 0 1 1 1
  | 10 => tabC3S36 0 1 2 0
  | 11 => tabC3S36 0 1 2 2
  | _ => tabC3S36 0 2 0 0
def memRowC3S361 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 0 2 0 1
  | 1 => tabC3S36 0 2 0 2
  | 2 => tabC3S36 0 2 1 0
  | 3 => tabC3S36 0 2 1 1
  | 4 => tabC3S36 0 2 1 2
  | 5 => tabC3S36 0 2 2 0
  | 6 => tabC3S36 0 2 2 1
  | 7 => tabC3S36 0 2 2 2
  | 8 => tabC3S36 0 3 0 0
  | 9 => tabC3S36 0 3 0 1
  | 10 => tabC3S36 0 3 0 2
  | 11 => tabC3S36 0 3 1 0
  | _ => tabC3S36 0 3 1 1
def memRowC3S362 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 0 3 1 2
  | 1 => tabC3S36 0 3 2 0
  | 2 => tabC3S36 0 3 2 1
  | 3 => tabC3S36 0 3 2 2
  | 4 => tabC3S36 0 4 0 0
  | 5 => tabC3S36 0 4 0 1
  | 6 => tabC3S36 0 4 0 2
  | 7 => tabC3S36 0 4 1 0
  | 8 => tabC3S36 0 4 1 1
  | 9 => tabC3S36 0 4 1 2
  | 10 => tabC3S36 0 4 2 0
  | 11 => tabC3S36 0 4 2 1
  | _ => tabC3S36 0 4 2 2
def memRowC3S363 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 0 5 0 0
  | 1 => tabC3S36 0 5 0 1
  | 2 => tabC3S36 0 5 0 2
  | 3 => tabC3S36 0 5 1 0
  | 4 => tabC3S36 0 5 1 1
  | 5 => tabC3S36 0 5 1 2
  | 6 => tabC3S36 0 5 2 0
  | 7 => tabC3S36 0 5 2 1
  | 8 => tabC3S36 0 5 2 2
  | 9 => tabC3S36 1 0 0 0
  | 10 => tabC3S36 1 0 0 1
  | 11 => tabC3S36 1 0 0 2
  | _ => tabC3S36 1 0 1 0
def memRowC3S364 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 1 0 1 1
  | 1 => tabC3S36 1 0 1 2
  | 2 => tabC3S36 1 0 2 0
  | 3 => tabC3S36 1 0 2 1
  | 4 => tabC3S36 1 0 2 2
  | 5 => tabC3S36 1 1 0 0
  | 6 => tabC3S36 1 1 0 1
  | 7 => tabC3S36 1 1 0 2
  | 8 => tabC3S36 1 1 1 0
  | 9 => tabC3S36 1 1 1 1
  | 10 => tabC3S36 1 1 1 2
  | 11 => tabC3S36 1 1 2 0
  | _ => tabC3S36 1 1 2 1
def memRowC3S365 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 1 1 2 2
  | 1 => tabC3S36 1 2 0 0
  | 2 => tabC3S36 1 2 0 1
  | 3 => tabC3S36 1 2 0 2
  | 4 => tabC3S36 1 2 1 0
  | 5 => tabC3S36 1 2 1 1
  | 6 => tabC3S36 1 2 1 2
  | 7 => tabC3S36 1 2 2 0
  | 8 => tabC3S36 1 2 2 1
  | 9 => tabC3S36 1 2 2 2
  | 10 => tabC3S36 1 3 0 0
  | 11 => tabC3S36 1 3 0 1
  | _ => tabC3S36 1 3 0 2
def memRowC3S366 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 1 3 1 0
  | 1 => tabC3S36 1 3 1 1
  | 2 => tabC3S36 1 3 1 2
  | 3 => tabC3S36 1 3 2 0
  | 4 => tabC3S36 1 3 2 1
  | 5 => tabC3S36 1 3 2 2
  | 6 => tabC3S36 1 4 0 0
  | 7 => tabC3S36 1 4 0 1
  | 8 => tabC3S36 1 4 0 2
  | 9 => tabC3S36 1 4 1 0
  | 10 => tabC3S36 1 4 1 1
  | 11 => tabC3S36 1 4 1 2
  | _ => tabC3S36 1 4 2 0
def memRowC3S367 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 1 4 2 1
  | 1 => tabC3S36 1 4 2 2
  | 2 => tabC3S36 1 5 0 0
  | 3 => tabC3S36 1 5 0 1
  | 4 => tabC3S36 1 5 0 2
  | 5 => tabC3S36 1 5 1 0
  | 6 => tabC3S36 1 5 1 1
  | 7 => tabC3S36 1 5 1 2
  | 8 => tabC3S36 1 5 2 0
  | 9 => tabC3S36 1 5 2 1
  | 10 => tabC3S36 1 5 2 2
  | 11 => tabC3S36 2 0 0 0
  | _ => tabC3S36 2 0 0 1
def memRowC3S368 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 2 0 0 2
  | 1 => tabC3S36 2 0 1 0
  | 2 => tabC3S36 2 0 1 1
  | 3 => tabC3S36 2 0 1 2
  | 4 => tabC3S36 2 0 2 0
  | 5 => tabC3S36 2 0 2 1
  | 6 => tabC3S36 2 0 2 2
  | 7 => tabC3S36 2 1 0 0
  | 8 => tabC3S36 2 1 0 1
  | 9 => tabC3S36 2 1 0 2
  | 10 => tabC3S36 2 1 1 0
  | 11 => tabC3S36 2 1 1 1
  | _ => tabC3S36 2 1 1 2
def memRowC3S369 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 2 1 2 0
  | 1 => tabC3S36 2 1 2 1
  | 2 => tabC3S36 2 1 2 2
  | 3 => tabC3S36 2 2 0 0
  | 4 => tabC3S36 2 2 0 1
  | 5 => tabC3S36 2 2 0 2
  | 6 => tabC3S36 2 2 1 0
  | 7 => tabC3S36 2 2 1 1
  | 8 => tabC3S36 2 2 1 2
  | 9 => tabC3S36 2 2 2 0
  | 10 => tabC3S36 2 2 2 1
  | 11 => tabC3S36 2 2 2 2
  | _ => tabC3S36 2 3 0 0
def memRowC3S3610 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 2 3 0 1
  | 1 => tabC3S36 2 3 0 2
  | 2 => tabC3S36 2 3 1 0
  | 3 => tabC3S36 2 3 1 1
  | 4 => tabC3S36 2 3 1 2
  | 5 => tabC3S36 2 3 2 0
  | 6 => tabC3S36 2 3 2 1
  | 7 => tabC3S36 2 3 2 2
  | 8 => tabC3S36 2 4 0 0
  | 9 => tabC3S36 2 4 0 1
  | 10 => tabC3S36 2 4 0 2
  | 11 => tabC3S36 2 4 1 0
  | _ => tabC3S36 2 4 1 1
def memRowC3S3611 : Fin 13 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC3S36 2 4 1 2
  | 1 => tabC3S36 2 4 2 0
  | 2 => tabC3S36 2 4 2 1
  | 3 => tabC3S36 2 4 2 2
  | 4 => tabC3S36 2 5 0 0
  | 5 => tabC3S36 2 5 0 1
  | 6 => tabC3S36 2 5 0 2
  | 7 => tabC3S36 2 5 1 0
  | 8 => tabC3S36 2 5 1 1
  | 9 => tabC3S36 2 5 1 2
  | 10 => tabC3S36 2 5 2 0
  | 11 => tabC3S36 2 5 2 1
  | _ => tabC3S36 2 5 2 2
def memC3S36 (i : Fin 156) : Fin 6 → Fin 6 → Fin 6 :=
  match (i.1 / 13 : Nat) with
  | 0 => memRowC3S360 ⟨i.1 % 13, by omega⟩
  | 1 => memRowC3S361 ⟨i.1 % 13, by omega⟩
  | 2 => memRowC3S362 ⟨i.1 % 13, by omega⟩
  | 3 => memRowC3S363 ⟨i.1 % 13, by omega⟩
  | 4 => memRowC3S364 ⟨i.1 % 13, by omega⟩
  | 5 => memRowC3S365 ⟨i.1 % 13, by omega⟩
  | 6 => memRowC3S366 ⟨i.1 % 13, by omega⟩
  | 7 => memRowC3S367 ⟨i.1 % 13, by omega⟩
  | 8 => memRowC3S368 ⟨i.1 % 13, by omega⟩
  | 9 => memRowC3S369 ⟨i.1 % 13, by omega⟩
  | 10 => memRowC3S3610 ⟨i.1 % 13, by omega⟩
  | _ => memRowC3S3611 ⟨i.1 % 13, by omega⟩

/-- Which of the `156` members a given invariant tuple is, so that `mem_of_isExactC3S36` can name
one rather than search the list for it. Read only by `native_decide`. -/
def rankArrC3S36 : Array Nat := #[
  0, 0, 1, 2, 3, 0, 4, 0, 5, 0, 6, 7, 8, 9, 0, 10, 0, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
  22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
  46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
  70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
  94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
  114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132,
  133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151,
  152, 153, 154, 155]

/-- The arguments as one mixed-radix index, which is how `rankArrC3S36` is addressed. -/
def encTC3S36 (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Nat :=
  a.1 * 54 +
    b.1 * 9 +
    c.1 * 3 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankC3S36 (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Fin 156 :=
  ⟨min (rankArrC3S36.getD (encTC3S36 a b c d) 0) 155, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactC3S36 (i : Fin 156) : Magma (Fin 6) := Magma.mk (memC3S36 i)

theorem exactC3S36_isEndo (i : Fin 156) (j : Fin 18) : (exactC3S36 i).IsEndo ⇑(eEC3S36 j) := by
  simp only [eEC3S36, coe_permOf]; revert i j; native_decide

theorem exactC3S36_not_isEndo (i : Fin 156) (j : Fin 1) : ¬ (exactC3S36 i).IsEndo ⇑(eXC3S36 j) := by
  simp only [eXC3S36, coe_permOf]; revert i j; native_decide

/-- `rankC3S36` really does name the member a tuple is. Deciding this is one array read and one
table comparison per tuple, where searching `memC3S36` for the index would be a comparison per tuple
and member. -/
theorem mem_rankC3S36 (a : Fin 3) (b : Fin 6) (c d : Fin 3)
    (h : Magma.isExact (tabC3S36 a b c d) permEC3S36 permXC3S36 = true) :
    memC3S36 (rankC3S36 a b c d) = tabC3S36 a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `156`
listed members. -/
theorem mem_of_isExactC3S36 (a : Fin 3) (b : Fin 6) (c d : Fin 3)
    (h : Magma.isExact (tabC3S36 a b c d) permEC3S36 permXC3S36 = true) :
    ∃ i, memC3S36 i = tabC3S36 a b c d :=
  ⟨_, mem_rankC3S36 a b c d h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactC3S36`. Its values at the orbit representatives name an invariant
tuple, and `mem_of_isExactC3S36` turns that into a member index. -/
theorem exists_exactC3S36 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eEC3S36 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXC3S36 i)) : ∃ i, exactC3S36 i = M := by
  simp only [eEC3S36, coe_permOf] at hE
  simp only [eXC3S36, coe_permOf] at hX
  have hop : M.op =
      Magma.transport permEC3S36 trC3S36 (fun i ↦ M.op (repC3S36 i).1 (repC3S36 i).2) :=
    Magma.op_eq_transport (rep := repC3S36) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEC3S36) (idx := stabIdxC3S360) (a := (repC3S36 0).1) (b := (repC3S36 0).2)
    (val := valC3S360) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEC3S36) (idx := stabIdxC3S361) (a := (repC3S36 1).1) (b := (repC3S36 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEC3S36) (idx := stabIdxC3S362) (a := (repC3S36 2).1) (b := (repC3S36 2).2)
    (val := valC3S362) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEC3S36) (idx := stabIdxC3S363) (a := (repC3S36 3).1) (b := (repC3S36 3).2)
    (val := valC3S363) hE (by decide) (by decide)
  have hdec : decC3S36 a b c d = fun i ↦ M.op (repC3S36 i).1 (repC3S36 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tabC3S36 a b c d = M.op := by
    rw [tabC3S36_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabC3S36 a b c d) permEC3S36 permXC3S36 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactC3S36 a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`18` group of `Magma.permEC3S36`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactC3S36 {L L' : Law.NatMagmaLaw} {i : Fin 156}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactC3S36 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactC3S36 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactC3S36 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactC3S36
    (fun k ↦ (Magma.exactC3S36_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactC3S36_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
