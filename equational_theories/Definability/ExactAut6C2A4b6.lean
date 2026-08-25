import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `C2A4b6` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 3)(1 2)(4 5), (0 4)(1 2)(3 5), (0 5)(1 2)(3 4), (1 2)(3 4 5)⟩` -/

/-- The `24` elements of the group: `()`, `(3 4 5)`, `(3 5 4)`, `(1 2)`, `(1 2)(3 4 5)`, `(1 2)(3 5
4)`, `(0 3)(4 5)`, `(0 3 4)`, `(0 3 5)`, `(0 3)(1 2)(4 5)`, `(0 3 4)(1 2)`, `(0 3 5)(1 2)`, `(0 4
3)`, `(0 4 5)`, `(0 4)(3 5)`, `(0 4 3)(1 2)`, `(0 4 5)(1 2)`, `(0 4)(1 2)(3 5)`, `(0 5 3)`, `(0 5
4)`, `(0 5)(3 4)`, `(0 5 3)(1 2)`, `(0 5 4)(1 2)`, `(0 5)(1 2)(3 4)`. -/
def pEC2A4b60 : Fin 6 → Fin 6 := id
def pEC2A4b61 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pEC2A4b62 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pEC2A4b63 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5
def pEC2A4b64 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 5 | 5 => 3
def pEC2A4b65 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pEC2A4b66 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4
def pEC2A4b67 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5
def pEC2A4b68 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 0
def pEC2A4b69 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4
def pEC2A4b610 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5
def pEC2A4b611 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 0
def pEC2A4b612 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5
def pEC2A4b613 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 0
def pEC2A4b614 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 0 | 5 => 3
def pEC2A4b615 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5
def pEC2A4b616 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 0
def pEC2A4b617 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 0 | 5 => 3
def pEC2A4b618 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 3
def pEC2A4b619 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 4
def pEC2A4b620 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 0
def pEC2A4b621 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 3
def pEC2A4b622 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 4
def pEC2A4b623 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 0

def permEC2A4b6 : Fin 24 → Fin 6 → Fin 6
  | 0 => pEC2A4b60
  | 1 => pEC2A4b61
  | 2 => pEC2A4b62
  | 3 => pEC2A4b63
  | 4 => pEC2A4b64
  | 5 => pEC2A4b65
  | 6 => pEC2A4b66
  | 7 => pEC2A4b67
  | 8 => pEC2A4b68
  | 9 => pEC2A4b69
  | 10 => pEC2A4b610
  | 11 => pEC2A4b611
  | 12 => pEC2A4b612
  | 13 => pEC2A4b613
  | 14 => pEC2A4b614
  | 15 => pEC2A4b615
  | 16 => pEC2A4b616
  | 17 => pEC2A4b617
  | 18 => pEC2A4b618
  | 19 => pEC2A4b619
  | 20 => pEC2A4b620
  | 21 => pEC2A4b621
  | 22 => pEC2A4b622
  | _ => pEC2A4b623

def permEinvC2A4b6 : Fin 24 → Fin 6 → Fin 6
  | 0 => pEC2A4b60
  | 1 => pEC2A4b62
  | 2 => pEC2A4b61
  | 3 => pEC2A4b63
  | 4 => pEC2A4b65
  | 5 => pEC2A4b64
  | 6 => pEC2A4b66
  | 7 => pEC2A4b612
  | 8 => pEC2A4b618
  | 9 => pEC2A4b69
  | 10 => pEC2A4b615
  | 11 => pEC2A4b621
  | 12 => pEC2A4b67
  | 13 => pEC2A4b619
  | 14 => pEC2A4b614
  | 15 => pEC2A4b610
  | 16 => pEC2A4b622
  | 17 => pEC2A4b617
  | 18 => pEC2A4b68
  | 19 => pEC2A4b613
  | 20 => pEC2A4b620
  | 21 => pEC2A4b611
  | 22 => pEC2A4b616
  | _ => pEC2A4b623

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEC2A4b6 (i : Fin 24) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permEC2A4b6 i) (permEinvC2A4b6 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 5)`. Every subgroup properly containing
the group above contains it, so a magma admitting the group and not this has that group as its
automorphism group exactly. -/
def pXC2A4b60 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0
def pXC2A4b60inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0

def permXC2A4b6 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXC2A4b60

def permXinvC2A4b6 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXC2A4b60inv

def eXC2A4b6 (i : Fin 1) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXC2A4b6 i) (permXinvC2A4b6 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `6`, so an invariant
operation is `6` values. -/
def repC2A4b6 : Fin 6 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trC2A4b6 : Fin 6 → Fin 6 → Fin 6 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 3)
  | 0, 3 => (2, 0)
  | 0, 4 => (2, 1)
  | 0, 5 => (2, 2)
  | 1, 0 => (3, 0)
  | 1, 1 => (4, 0)
  | 1, 2 => (5, 0)
  | 1, 3 => (3, 6)
  | 1, 4 => (3, 12)
  | 1, 5 => (3, 18)
  | 2, 0 => (3, 3)
  | 2, 1 => (5, 3)
  | 2, 2 => (4, 3)
  | 2, 3 => (3, 9)
  | 2, 4 => (3, 15)
  | 2, 5 => (3, 21)
  | 3, 0 => (2, 6)
  | 3, 1 => (1, 6)
  | 3, 2 => (1, 9)
  | 3, 3 => (0, 6)
  | 3, 4 => (2, 7)
  | 3, 5 => (2, 8)
  | 4, 0 => (2, 12)
  | 4, 1 => (1, 12)
  | 4, 2 => (1, 15)
  | 4, 3 => (2, 13)
  | 4, 4 => (0, 12)
  | 4, 5 => (2, 14)
  | 5, 0 => (2, 18)
  | 5, 1 => (1, 18)
  | 5, 2 => (1, 21)
  | 5, 3 => (2, 19)
  | 5, 4 => (2, 20)
  | 5, 5 => (0, 18)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxC2A4b60 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valC2A4b60 : Fin 1 → Fin 6
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxC2A4b61 : Fin 3 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valC2A4b61 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdxC2A4b62 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 3
def valC2A4b62 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `3` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxC2A4b63 : Fin 3 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valC2A4b63 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `12` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxC2A4b64 : Fin 12 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 12
  | 7 => 13
  | 8 => 14
  | 9 => 18
  | 10 => 19
  | 11 => 20
def valC2A4b64 : Fin 2 → Fin 6
  | 0 => 1
  | 1 => 2

/-- The `12` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxC2A4b65 : Fin 12 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 12
  | 7 => 13
  | 8 => 14
  | 9 => 18
  | 10 => 19
  | 11 => 20
def valC2A4b65 : Fin 2 → Fin 6
  | 0 => 1
  | 1 => 2

/-- The `6` orbit values named by the family's arguments. -/
def decC2A4b6 (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2) : Fin 6 → Fin 6
  | 0 => valC2A4b60 a
  | 1 => valC2A4b61 b
  | 2 => valC2A4b62 c
  | 3 => valC2A4b63 d
  | 4 => valC2A4b64 e
  | 5 => valC2A4b65 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabC2A4b6_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabC2A4b6 (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valC2A4b60 a
  | 0, 1 => valC2A4b61 b
  | 0, 2 => pEC2A4b63 (valC2A4b61 b)
  | 0, 3 => valC2A4b62 c
  | 0, 4 => pEC2A4b61 (valC2A4b62 c)
  | 0, 5 => pEC2A4b62 (valC2A4b62 c)
  | 1, 0 => valC2A4b63 d
  | 1, 1 => valC2A4b64 e
  | 1, 2 => valC2A4b65 f
  | 1, 3 => pEC2A4b66 (valC2A4b63 d)
  | 1, 4 => pEC2A4b612 (valC2A4b63 d)
  | 1, 5 => pEC2A4b618 (valC2A4b63 d)
  | 2, 0 => pEC2A4b63 (valC2A4b63 d)
  | 2, 1 => pEC2A4b63 (valC2A4b65 f)
  | 2, 2 => pEC2A4b63 (valC2A4b64 e)
  | 2, 3 => pEC2A4b69 (valC2A4b63 d)
  | 2, 4 => pEC2A4b615 (valC2A4b63 d)
  | 2, 5 => pEC2A4b621 (valC2A4b63 d)
  | 3, 0 => pEC2A4b66 (valC2A4b62 c)
  | 3, 1 => pEC2A4b66 (valC2A4b61 b)
  | 3, 2 => pEC2A4b69 (valC2A4b61 b)
  | 3, 3 => pEC2A4b66 (valC2A4b60 a)
  | 3, 4 => pEC2A4b67 (valC2A4b62 c)
  | 3, 5 => pEC2A4b68 (valC2A4b62 c)
  | 4, 0 => pEC2A4b612 (valC2A4b62 c)
  | 4, 1 => pEC2A4b612 (valC2A4b61 b)
  | 4, 2 => pEC2A4b615 (valC2A4b61 b)
  | 4, 3 => pEC2A4b613 (valC2A4b62 c)
  | 4, 4 => pEC2A4b612 (valC2A4b60 a)
  | 4, 5 => pEC2A4b614 (valC2A4b62 c)
  | 5, 0 => pEC2A4b618 (valC2A4b62 c)
  | 5, 1 => pEC2A4b618 (valC2A4b61 b)
  | 5, 2 => pEC2A4b621 (valC2A4b61 b)
  | 5, 3 => pEC2A4b619 (valC2A4b62 c)
  | 5, 4 => pEC2A4b620 (valC2A4b62 c)
  | 5, 5 => pEC2A4b618 (valC2A4b60 a)

theorem tabC2A4b6_eq_transport (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2) :
    tabC2A4b6 a b c d e f = Magma.transport permEC2A4b6 trC2A4b6 (decC2A4b6 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `72` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `144` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowC2A4b60 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 0 2 0 0 0
  | 1 => tabC2A4b6 0 0 2 0 0 1
  | 2 => tabC2A4b6 0 0 2 0 1 0
  | 3 => tabC2A4b6 0 0 2 0 1 1
  | 4 => tabC2A4b6 0 0 2 1 0 0
  | 5 => tabC2A4b6 0 0 2 1 0 1
  | 6 => tabC2A4b6 0 0 2 1 1 0
  | 7 => tabC2A4b6 0 0 2 1 1 1
  | _ => tabC2A4b6 0 0 2 2 0 0
def memRowC2A4b61 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 0 2 2 0 1
  | 1 => tabC2A4b6 0 0 2 2 1 0
  | 2 => tabC2A4b6 0 0 2 2 1 1
  | 3 => tabC2A4b6 0 0 3 0 0 0
  | 4 => tabC2A4b6 0 0 3 0 0 1
  | 5 => tabC2A4b6 0 0 3 0 1 0
  | 6 => tabC2A4b6 0 0 3 0 1 1
  | 7 => tabC2A4b6 0 0 3 1 0 0
  | _ => tabC2A4b6 0 0 3 1 0 1
def memRowC2A4b62 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 0 3 1 1 0
  | 1 => tabC2A4b6 0 0 3 1 1 1
  | 2 => tabC2A4b6 0 0 3 2 0 0
  | 3 => tabC2A4b6 0 0 3 2 0 1
  | 4 => tabC2A4b6 0 0 3 2 1 0
  | 5 => tabC2A4b6 0 0 3 2 1 1
  | 6 => tabC2A4b6 0 1 2 0 0 0
  | 7 => tabC2A4b6 0 1 2 0 0 1
  | _ => tabC2A4b6 0 1 2 0 1 0
def memRowC2A4b63 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 1 2 0 1 1
  | 1 => tabC2A4b6 0 1 2 1 0 0
  | 2 => tabC2A4b6 0 1 2 1 0 1
  | 3 => tabC2A4b6 0 1 2 1 1 0
  | 4 => tabC2A4b6 0 1 2 1 1 1
  | 5 => tabC2A4b6 0 1 2 2 0 0
  | 6 => tabC2A4b6 0 1 2 2 0 1
  | 7 => tabC2A4b6 0 1 2 2 1 0
  | _ => tabC2A4b6 0 1 2 2 1 1
def memRowC2A4b64 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 1 3 0 0 0
  | 1 => tabC2A4b6 0 1 3 0 0 1
  | 2 => tabC2A4b6 0 1 3 0 1 0
  | 3 => tabC2A4b6 0 1 3 0 1 1
  | 4 => tabC2A4b6 0 1 3 1 0 0
  | 5 => tabC2A4b6 0 1 3 1 0 1
  | 6 => tabC2A4b6 0 1 3 1 1 0
  | 7 => tabC2A4b6 0 1 3 1 1 1
  | _ => tabC2A4b6 0 1 3 2 0 0
def memRowC2A4b65 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 1 3 2 0 1
  | 1 => tabC2A4b6 0 1 3 2 1 0
  | 2 => tabC2A4b6 0 1 3 2 1 1
  | 3 => tabC2A4b6 0 2 2 0 0 0
  | 4 => tabC2A4b6 0 2 2 0 0 1
  | 5 => tabC2A4b6 0 2 2 0 1 0
  | 6 => tabC2A4b6 0 2 2 0 1 1
  | 7 => tabC2A4b6 0 2 2 1 0 0
  | _ => tabC2A4b6 0 2 2 1 0 1
def memRowC2A4b66 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 2 2 1 1 0
  | 1 => tabC2A4b6 0 2 2 1 1 1
  | 2 => tabC2A4b6 0 2 2 2 0 0
  | 3 => tabC2A4b6 0 2 2 2 0 1
  | 4 => tabC2A4b6 0 2 2 2 1 0
  | 5 => tabC2A4b6 0 2 2 2 1 1
  | 6 => tabC2A4b6 0 2 3 0 0 0
  | 7 => tabC2A4b6 0 2 3 0 0 1
  | _ => tabC2A4b6 0 2 3 0 1 0
def memRowC2A4b67 : Fin 9 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A4b6 0 2 3 0 1 1
  | 1 => tabC2A4b6 0 2 3 1 0 0
  | 2 => tabC2A4b6 0 2 3 1 0 1
  | 3 => tabC2A4b6 0 2 3 1 1 0
  | 4 => tabC2A4b6 0 2 3 1 1 1
  | 5 => tabC2A4b6 0 2 3 2 0 0
  | 6 => tabC2A4b6 0 2 3 2 0 1
  | 7 => tabC2A4b6 0 2 3 2 1 0
  | _ => tabC2A4b6 0 2 3 2 1 1
def memC2A4b6 (i : Fin 72) : Fin 6 → Fin 6 → Fin 6 :=
  match (i.1 / 9 : Nat) with
  | 0 => memRowC2A4b60 ⟨i.1 % 9, by omega⟩
  | 1 => memRowC2A4b61 ⟨i.1 % 9, by omega⟩
  | 2 => memRowC2A4b62 ⟨i.1 % 9, by omega⟩
  | 3 => memRowC2A4b63 ⟨i.1 % 9, by omega⟩
  | 4 => memRowC2A4b64 ⟨i.1 % 9, by omega⟩
  | 5 => memRowC2A4b65 ⟨i.1 % 9, by omega⟩
  | 6 => memRowC2A4b66 ⟨i.1 % 9, by omega⟩
  | _ => memRowC2A4b67 ⟨i.1 % 9, by omega⟩

/-- Which of the `72` members a given invariant tuple is, so that `mem_of_isExactC2A4b6` can name
one rather than search the list for it. Read only by `native_decide`. -/
def rankArrC2A4b6 : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7,
  8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
  38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66,
  67, 68, 69, 70, 71]

/-- The arguments as one mixed-radix index, which is how `rankArrC2A4b6` is addressed. -/
def encTC2A4b6 (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2) : Nat :=
  a.1 * 144 +
    b.1 * 48 +
    c.1 * 12 +
    d.1 * 4 +
    e.1 * 2 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankC2A4b6 (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2) : Fin 72 :=
  ⟨min (rankArrC2A4b6.getD (encTC2A4b6 a b c d e f) 0) 71, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactC2A4b6 (i : Fin 72) : Magma (Fin 6) := Magma.mk (memC2A4b6 i)

theorem exactC2A4b6_isEndo (i : Fin 72) (j : Fin 24) : (exactC2A4b6 i).IsEndo ⇑(eEC2A4b6 j) := by
  simp only [eEC2A4b6, coe_permOf]; revert i j; native_decide

theorem exactC2A4b6_not_isEndo (i : Fin 72) (j : Fin 1)
    : ¬ (exactC2A4b6 i).IsEndo ⇑(eXC2A4b6 j) := by
  simp only [eXC2A4b6, coe_permOf]; revert i j; native_decide

/-- `rankC2A4b6` really does name the member a tuple is. Deciding this is one array read and one
table comparison per tuple, where searching `memC2A4b6` for the index would be a comparison per
tuple and member. -/
theorem mem_rankC2A4b6 (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2)
    (h : Magma.isExact (tabC2A4b6 a b c d e f) permEC2A4b6 permXC2A4b6 = true) :
    memC2A4b6 (rankC2A4b6 a b c d e f) = tabC2A4b6 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `72` listed
members. -/
theorem mem_of_isExactC2A4b6 (a : Fin 1) (b : Fin 3) (c : Fin 4) (d : Fin 3) (e f : Fin 2)
    (h : Magma.isExact (tabC2A4b6 a b c d e f) permEC2A4b6 permXC2A4b6 = true) :
    ∃ i, memC2A4b6 i = tabC2A4b6 a b c d e f :=
  ⟨_, mem_rankC2A4b6 a b c d e f h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactC2A4b6`. Its values at the orbit representatives name an invariant
tuple, and `mem_of_isExactC2A4b6` turns that into a member index. -/
theorem exists_exactC2A4b6 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eEC2A4b6 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXC2A4b6 i)) : ∃ i, exactC2A4b6 i = M := by
  simp only [eEC2A4b6, coe_permOf] at hE
  simp only [eXC2A4b6, coe_permOf] at hX
  have hop : M.op =
      Magma.transport permEC2A4b6 trC2A4b6 (fun i ↦ M.op (repC2A4b6 i).1 (repC2A4b6 i).2) :=
    Magma.op_eq_transport (rep := repC2A4b6) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A4b6) (idx := stabIdxC2A4b60) (a := (repC2A4b6 0).1) (b := (repC2A4b6 0).2)
    (val := valC2A4b60) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A4b6) (idx := stabIdxC2A4b61) (a := (repC2A4b6 1).1) (b := (repC2A4b6 1).2)
    (val := valC2A4b61) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A4b6) (idx := stabIdxC2A4b62) (a := (repC2A4b6 2).1) (b := (repC2A4b6 2).2)
    (val := valC2A4b62) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A4b6) (idx := stabIdxC2A4b63) (a := (repC2A4b6 3).1) (b := (repC2A4b6 3).2)
    (val := valC2A4b63) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A4b6) (idx := stabIdxC2A4b64) (a := (repC2A4b6 4).1) (b := (repC2A4b6 4).2)
    (val := valC2A4b64) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A4b6) (idx := stabIdxC2A4b65) (a := (repC2A4b6 5).1) (b := (repC2A4b6 5).2)
    (val := valC2A4b65) hE (by decide) (by decide)
  have hdec : decC2A4b6 a b c d e f = fun i ↦ M.op (repC2A4b6 i).1 (repC2A4b6 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabC2A4b6 a b c d e f = M.op := by
    rw [tabC2A4b6_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabC2A4b6 a b c d e f) permEC2A4b6 permXC2A4b6 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactC2A4b6 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`24` group of `Magma.permEC2A4b6`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactC2A4b6 {L L' : Law.NatMagmaLaw} {i : Fin 72}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactC2A4b6 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactC2A4b6 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactC2A4b6 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactC2A4b6
    (fun k ↦ (Magma.exactC2A4b6_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactC2A4b6_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
