import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S3sq6` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`36` group `⟨(0 1 2)(3 4 5), (0 1 2)(3 5 4), (1 2)(3 4 5), (0 1 2)(4 5)⟩` -/

/-- The `36` elements of the group: `()`, `(4 5)`, `(3 4)`, `(3 4 5)`, `(3 5 4)`, `(3 5)`, `(1 2)`,
`(1 2)(4 5)`, `(1 2)(3 4)`, `(1 2)(3 4 5)`, `(1 2)(3 5 4)`, `(1 2)(3 5)`, `(0 1)`, `(0 1)(4 5)`, `(0
1)(3 4)`, `(0 1)(3 4 5)`, `(0 1)(3 5 4)`, `(0 1)(3 5)`, `(0 1 2)`, `(0 1 2)(4 5)`, `(0 1 2)(3 4)`,
`(0 1 2)(3 4 5)`, `(0 1 2)(3 5 4)`, `(0 1 2)(3 5)`, `(0 2 1)`, `(0 2 1)(4 5)`, `(0 2 1)(3 4)`, `(0 2
1)(3 4 5)`, `(0 2 1)(3 5 4)`, `(0 2 1)(3 5)`, `(0 2)`, `(0 2)(4 5)`, `(0 2)(3 4)`, `(0 2)(3 4 5)`,
`(0 2)(3 5 4)`, `(0 2)(3 5)`. -/
def pES3sq60 : Fin 6 → Fin 6 := id
def pES3sq61 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pES3sq62 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pES3sq63 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pES3sq64 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pES3sq65 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pES3sq66 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5
def pES3sq67 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pES3sq68 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5
def pES3sq69 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 5 | 5 => 3
def pES3sq610 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pES3sq611 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
def pES3sq612 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pES3sq613 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pES3sq614 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pES3sq615 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 3
def pES3sq616 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 4
def pES3sq617 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pES3sq618 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5
def pES3sq619 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pES3sq620 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5
def pES3sq621 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pES3sq622 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 4
def pES3sq623 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3
def pES3sq624 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5
def pES3sq625 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pES3sq626 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5
def pES3sq627 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 5 | 5 => 3
def pES3sq628 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pES3sq629 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
def pES3sq630 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5
def pES3sq631 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pES3sq632 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5
def pES3sq633 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pES3sq634 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 4
def pES3sq635 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3

def permES3sq6 : Fin 36 → Fin 6 → Fin 6
  | 0 => pES3sq60
  | 1 => pES3sq61
  | 2 => pES3sq62
  | 3 => pES3sq63
  | 4 => pES3sq64
  | 5 => pES3sq65
  | 6 => pES3sq66
  | 7 => pES3sq67
  | 8 => pES3sq68
  | 9 => pES3sq69
  | 10 => pES3sq610
  | 11 => pES3sq611
  | 12 => pES3sq612
  | 13 => pES3sq613
  | 14 => pES3sq614
  | 15 => pES3sq615
  | 16 => pES3sq616
  | 17 => pES3sq617
  | 18 => pES3sq618
  | 19 => pES3sq619
  | 20 => pES3sq620
  | 21 => pES3sq621
  | 22 => pES3sq622
  | 23 => pES3sq623
  | 24 => pES3sq624
  | 25 => pES3sq625
  | 26 => pES3sq626
  | 27 => pES3sq627
  | 28 => pES3sq628
  | 29 => pES3sq629
  | 30 => pES3sq630
  | 31 => pES3sq631
  | 32 => pES3sq632
  | 33 => pES3sq633
  | 34 => pES3sq634
  | _ => pES3sq635

def permEinvS3sq6 : Fin 36 → Fin 6 → Fin 6
  | 0 => pES3sq60
  | 1 => pES3sq61
  | 2 => pES3sq62
  | 3 => pES3sq64
  | 4 => pES3sq63
  | 5 => pES3sq65
  | 6 => pES3sq66
  | 7 => pES3sq67
  | 8 => pES3sq68
  | 9 => pES3sq610
  | 10 => pES3sq69
  | 11 => pES3sq611
  | 12 => pES3sq612
  | 13 => pES3sq613
  | 14 => pES3sq614
  | 15 => pES3sq616
  | 16 => pES3sq615
  | 17 => pES3sq617
  | 18 => pES3sq624
  | 19 => pES3sq625
  | 20 => pES3sq626
  | 21 => pES3sq628
  | 22 => pES3sq627
  | 23 => pES3sq629
  | 24 => pES3sq618
  | 25 => pES3sq619
  | 26 => pES3sq620
  | 27 => pES3sq622
  | 28 => pES3sq621
  | 29 => pES3sq623
  | 30 => pES3sq630
  | 31 => pES3sq631
  | 32 => pES3sq632
  | 33 => pES3sq634
  | 34 => pES3sq633
  | _ => pES3sq635

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES3sq6 (i : Fin 36) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permES3sq6 i) (permEinvS3sq6 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 5)(1 4)(2 3)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXS3sq60 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0
def pXS3sq60inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0

def permXS3sq6 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXS3sq60

def permXinvS3sq6 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXS3sq60inv

def eXS3sq6 (i : Fin 1) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXS3sq6 i) (permXinvS3sq6 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `6`, so an invariant
operation is `6` values. -/
def repS3sq6 : Fin 6 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (3, 0)
  | 4 => (3, 3)
  | 5 => (3, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS3sq6 : Fin 6 → Fin 6 → Fin 6 × Fin 36
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 6)
  | 0, 3 => (2, 0)
  | 0, 4 => (2, 2)
  | 0, 5 => (2, 4)
  | 1, 0 => (1, 12)
  | 1, 1 => (0, 12)
  | 1, 2 => (1, 18)
  | 1, 3 => (2, 12)
  | 1, 4 => (2, 14)
  | 1, 5 => (2, 16)
  | 2, 0 => (1, 24)
  | 2, 1 => (1, 30)
  | 2, 2 => (0, 24)
  | 2, 3 => (2, 24)
  | 2, 4 => (2, 26)
  | 2, 5 => (2, 28)
  | 3, 0 => (3, 0)
  | 3, 1 => (3, 12)
  | 3, 2 => (3, 24)
  | 3, 3 => (4, 0)
  | 3, 4 => (5, 0)
  | 3, 5 => (5, 1)
  | 4, 0 => (3, 2)
  | 4, 1 => (3, 14)
  | 4, 2 => (3, 26)
  | 4, 3 => (5, 2)
  | 4, 4 => (4, 2)
  | 4, 5 => (5, 3)
  | 5, 0 => (3, 4)
  | 5, 1 => (3, 16)
  | 5, 2 => (3, 28)
  | 5, 3 => (5, 4)
  | 5, 4 => (5, 5)
  | 5, 5 => (4, 4)

/-- The `12` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS3sq60 : Fin 12 → Fin 36
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
def valS3sq60 : Fin 1 → Fin 6
  | 0 => 0

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS3sq61 : Fin 6 → Fin 36
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS3sq61 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS3sq62 : Fin 4 → Fin 36
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def valS3sq62 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS3sq63 : Fin 4 → Fin 36
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def valS3sq63 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `12` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be `3`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS3sq64 : Fin 12 → Fin 36
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
  | 4 => 12
  | 5 => 13
  | 6 => 18
  | 7 => 19
  | 8 => 24
  | 9 => 25
  | 10 => 30
  | 11 => 31
def valS3sq64 : Fin 1 → Fin 6
  | 0 => 3

/-- The `6` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `3`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS3sq65 : Fin 6 → Fin 36
  | 0 => 0
  | 1 => 6
  | 2 => 12
  | 3 => 18
  | 4 => 24
  | 5 => 30
def valS3sq65 : Fin 3 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5

/-- The `6` orbit values named by the family's arguments. -/
def decS3sq6 (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3) : Fin 6 → Fin 6
  | 0 => valS3sq60 a
  | 1 => valS3sq61 b
  | 2 => valS3sq62 c
  | 3 => valS3sq63 d
  | 4 => valS3sq64 e
  | 5 => valS3sq65 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS3sq6_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS3sq6 (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valS3sq60 a
  | 0, 1 => valS3sq61 b
  | 0, 2 => pES3sq66 (valS3sq61 b)
  | 0, 3 => valS3sq62 c
  | 0, 4 => pES3sq62 (valS3sq62 c)
  | 0, 5 => pES3sq64 (valS3sq62 c)
  | 1, 0 => pES3sq612 (valS3sq61 b)
  | 1, 1 => pES3sq612 (valS3sq60 a)
  | 1, 2 => pES3sq618 (valS3sq61 b)
  | 1, 3 => pES3sq612 (valS3sq62 c)
  | 1, 4 => pES3sq614 (valS3sq62 c)
  | 1, 5 => pES3sq616 (valS3sq62 c)
  | 2, 0 => pES3sq624 (valS3sq61 b)
  | 2, 1 => pES3sq630 (valS3sq61 b)
  | 2, 2 => pES3sq624 (valS3sq60 a)
  | 2, 3 => pES3sq624 (valS3sq62 c)
  | 2, 4 => pES3sq626 (valS3sq62 c)
  | 2, 5 => pES3sq628 (valS3sq62 c)
  | 3, 0 => valS3sq63 d
  | 3, 1 => pES3sq612 (valS3sq63 d)
  | 3, 2 => pES3sq624 (valS3sq63 d)
  | 3, 3 => valS3sq64 e
  | 3, 4 => valS3sq65 f
  | 3, 5 => pES3sq61 (valS3sq65 f)
  | 4, 0 => pES3sq62 (valS3sq63 d)
  | 4, 1 => pES3sq614 (valS3sq63 d)
  | 4, 2 => pES3sq626 (valS3sq63 d)
  | 4, 3 => pES3sq62 (valS3sq65 f)
  | 4, 4 => pES3sq62 (valS3sq64 e)
  | 4, 5 => pES3sq63 (valS3sq65 f)
  | 5, 0 => pES3sq64 (valS3sq63 d)
  | 5, 1 => pES3sq616 (valS3sq63 d)
  | 5, 2 => pES3sq628 (valS3sq63 d)
  | 5, 3 => pES3sq64 (valS3sq65 f)
  | 5, 4 => pES3sq65 (valS3sq65 f)
  | 5, 5 => pES3sq64 (valS3sq64 e)

theorem tabS3sq6_eq_transport (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3) :
    tabS3sq6 a b c d e f = Magma.transport permES3sq6 trS3sq6 (decS3sq6 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `30` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `36` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS3sq6 : Fin 30 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabS3sq6 0 0 0 0 0 0
  | 1 => tabS3sq6 0 0 0 0 0 1
  | 2 => tabS3sq6 0 0 0 0 0 2
  | 3 => tabS3sq6 0 0 0 1 0 1
  | 4 => tabS3sq6 0 0 0 1 0 2
  | 5 => tabS3sq6 0 0 1 0 0 1
  | 6 => tabS3sq6 0 0 1 0 0 2
  | 7 => tabS3sq6 0 0 1 1 0 0
  | 8 => tabS3sq6 0 0 1 1 0 1
  | 9 => tabS3sq6 0 0 1 1 0 2
  | 10 => tabS3sq6 0 1 0 0 0 0
  | 11 => tabS3sq6 0 1 0 0 0 1
  | 12 => tabS3sq6 0 1 0 0 0 2
  | 13 => tabS3sq6 0 1 0 1 0 0
  | 14 => tabS3sq6 0 1 0 1 0 2
  | 15 => tabS3sq6 0 1 1 0 0 0
  | 16 => tabS3sq6 0 1 1 0 0 2
  | 17 => tabS3sq6 0 1 1 1 0 0
  | 18 => tabS3sq6 0 1 1 1 0 1
  | 19 => tabS3sq6 0 1 1 1 0 2
  | 20 => tabS3sq6 0 2 0 0 0 0
  | 21 => tabS3sq6 0 2 0 0 0 1
  | 22 => tabS3sq6 0 2 0 0 0 2
  | 23 => tabS3sq6 0 2 0 1 0 0
  | 24 => tabS3sq6 0 2 0 1 0 1
  | 25 => tabS3sq6 0 2 1 0 0 0
  | 26 => tabS3sq6 0 2 1 0 0 1
  | 27 => tabS3sq6 0 2 1 1 0 0
  | 28 => tabS3sq6 0 2 1 1 0 1
  | _ => tabS3sq6 0 2 1 1 0 2

/-- Which of the `30` members a given invariant tuple is, so that `mem_of_isExactS3sq6` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS3sq6 : Array Nat := #[
  0, 1, 2, 0, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 14, 15, 0, 16, 17, 18, 19, 20, 21, 22,
  23, 24, 0, 25, 26, 0, 27, 28, 29]

/-- The arguments as one mixed-radix index, which is how `rankArrS3sq6` is addressed. -/
def encTS3sq6 (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3) : Nat :=
  a.1 * 36 +
    b.1 * 12 +
    c.1 * 6 +
    d.1 * 3 +
    e.1 * 3 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS3sq6 (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3) : Fin 30 :=
  ⟨min (rankArrS3sq6.getD (encTS3sq6 a b c d e f) 0) 29, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS3sq6 (i : Fin 30) : Magma (Fin 6) := Magma.mk (memS3sq6 i)

theorem exactS3sq6_isEndo (i : Fin 30) (j : Fin 36) : (exactS3sq6 i).IsEndo ⇑(eES3sq6 j) := by
  simp only [eES3sq6, coe_permOf]; revert i j; native_decide

theorem exactS3sq6_not_isEndo (i : Fin 30) (j : Fin 1) : ¬ (exactS3sq6 i).IsEndo ⇑(eXS3sq6 j) := by
  simp only [eXS3sq6, coe_permOf]; revert i j; native_decide

/-- `rankS3sq6` really does name the member a tuple is. Deciding this is one array read and one
table comparison per tuple, where searching `memS3sq6` for the index would be a comparison per tuple
and member. -/
theorem mem_rankS3sq6 (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3)
    (h : Magma.isExact (tabS3sq6 a b c d e f) permES3sq6 permXS3sq6 = true) :
    memS3sq6 (rankS3sq6 a b c d e f) = tabS3sq6 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `30` listed
members. -/
theorem mem_of_isExactS3sq6 (a : Fin 1) (b : Fin 3) (c d : Fin 2) (e : Fin 1) (f : Fin 3)
    (h : Magma.isExact (tabS3sq6 a b c d e f) permES3sq6 permXS3sq6 = true) :
    ∃ i, memS3sq6 i = tabS3sq6 a b c d e f :=
  ⟨_, mem_rankS3sq6 a b c d e f h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS3sq6`. Its values at the orbit representatives name an invariant
tuple, and `mem_of_isExactS3sq6` turns that into a member index. -/
theorem exists_exactS3sq6 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eES3sq6 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS3sq6 i)) : ∃ i, exactS3sq6 i = M := by
  simp only [eES3sq6, coe_permOf] at hE
  simp only [eXS3sq6, coe_permOf] at hX
  have hop : M.op =
      Magma.transport permES3sq6 trS3sq6 (fun i ↦ M.op (repS3sq6 i).1 (repS3sq6 i).2) :=
    Magma.op_eq_transport (rep := repS3sq6) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES3sq6) (idx := stabIdxS3sq60) (a := (repS3sq6 0).1) (b := (repS3sq6 0).2)
    (val := valS3sq60) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES3sq6) (idx := stabIdxS3sq61) (a := (repS3sq6 1).1) (b := (repS3sq6 1).2)
    (val := valS3sq61) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES3sq6) (idx := stabIdxS3sq62) (a := (repS3sq6 2).1) (b := (repS3sq6 2).2)
    (val := valS3sq62) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES3sq6) (idx := stabIdxS3sq63) (a := (repS3sq6 3).1) (b := (repS3sq6 3).2)
    (val := valS3sq63) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES3sq6) (idx := stabIdxS3sq64) (a := (repS3sq6 4).1) (b := (repS3sq6 4).2)
    (val := valS3sq64) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permES3sq6) (idx := stabIdxS3sq65) (a := (repS3sq6 5).1) (b := (repS3sq6 5).2)
    (val := valS3sq65) hE (by decide) (by decide)
  have hdec : decS3sq6 a b c d e f = fun i ↦ M.op (repS3sq6 i).1 (repS3sq6 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabS3sq6 a b c d e f = M.op := by
    rw [tabS3sq6_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS3sq6 a b c d e f) permES3sq6 permXS3sq6 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS3sq6 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`36` group of `Magma.permES3sq6`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS3sq6 {L L' : Law.NatMagmaLaw} {i : Fin 30}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactS3sq6 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactS3sq6 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS3sq6 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS3sq6
    (fun k ↦ (Magma.exactS3sq6_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS3sq6_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
