import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S4b7` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(1 2)(3 4 5 6), (1 3 2 5)(4 6)⟩` -/

/-- The `24` elements of the group: `()`, `(3 4)(5 6)`, `(3 5)(4 6)`, `(3 6)(4 5)`, `(1 2)(4 6)`,
`(1 2)(3 4 5 6)`, `(1 2)(3 5)`, `(1 2)(3 6 5 4)`, `(1 3)(2 5)`, `(1 3 2 5)(4 6)`, `(1 3 4)(2 5 6)`,
`(1 3 6)(2 5 4)`, `(1 4 3)(2 6 5)`, `(1 4 5)(2 6 3)`, `(1 4)(2 6)`, `(1 4 2 6)(3 5)`, `(1 5 2 3)(4
6)`, `(1 5)(2 3)`, `(1 5 6)(2 3 4)`, `(1 5 4)(2 3 6)`, `(1 6 3)(2 4 5)`, `(1 6 5)(2 4 3)`, `(1 6)(2
4)`, `(1 6 2 4)(3 5)`. -/
def pES4b70 : Fin 7 → Fin 7 := id
def pES4b71 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pES4b72 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4
def pES4b73 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 3
def pES4b74 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 5 | 6 => 4
def pES4b75 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 3
def pES4b76 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 6
def pES4b77 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 6 | 4 => 3 | 5 => 4 | 6 => 5
def pES4b78 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 2 | 6 => 6
def pES4b79 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 6 | 5 => 1 | 6 => 4
def pES4b710 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 2
def pES4b711 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 4 | 6 => 1
def pES4b712 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 5
def pES4b713 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 1 | 6 => 3
def pES4b714 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 2
def pES4b715 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 1
def pES4b716 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 2 | 6 => 4
def pES4b717 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 1 | 6 => 6
def pES4b718 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 1
def pES4b719 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 6 | 4 => 1 | 5 => 4 | 6 => 2
def pES4b720 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 2 | 6 => 3
def pES4b721 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1 | 6 => 5
def pES4b722 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 1
def pES4b723 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 2

def permES4b7 : Fin 24 → Fin 7 → Fin 7
  | 0 => pES4b70
  | 1 => pES4b71
  | 2 => pES4b72
  | 3 => pES4b73
  | 4 => pES4b74
  | 5 => pES4b75
  | 6 => pES4b76
  | 7 => pES4b77
  | 8 => pES4b78
  | 9 => pES4b79
  | 10 => pES4b710
  | 11 => pES4b711
  | 12 => pES4b712
  | 13 => pES4b713
  | 14 => pES4b714
  | 15 => pES4b715
  | 16 => pES4b716
  | 17 => pES4b717
  | 18 => pES4b718
  | 19 => pES4b719
  | 20 => pES4b720
  | 21 => pES4b721
  | 22 => pES4b722
  | _ => pES4b723

def permEinvS4b7 : Fin 24 → Fin 7 → Fin 7
  | 0 => pES4b70
  | 1 => pES4b71
  | 2 => pES4b72
  | 3 => pES4b73
  | 4 => pES4b74
  | 5 => pES4b77
  | 6 => pES4b76
  | 7 => pES4b75
  | 8 => pES4b78
  | 9 => pES4b716
  | 10 => pES4b712
  | 11 => pES4b720
  | 12 => pES4b710
  | 13 => pES4b719
  | 14 => pES4b714
  | 15 => pES4b723
  | 16 => pES4b79
  | 17 => pES4b717
  | 18 => pES4b721
  | 19 => pES4b713
  | 20 => pES4b711
  | 21 => pES4b718
  | 22 => pES4b722
  | _ => pES4b715

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES4b7 (i : Fin 24) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permES4b7 i) (permEinvS4b7 i) (by revert i; decide)

/-- The `4` permutations that must *not* be automorphisms: `(1 3)(2 6)`, `(1 5)(2 3)(4 6)`, `(0 4 1
6 3 5 2)`, `(0 6 2)(1 4 5)`. Every subgroup properly containing the group above contains one of
them, so a magma admitting the group and not these has that group as its automorphism group exactly.
-/
def pXS4b70 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2
def pXS4b71 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 1 | 6 => 4
def pXS4b72 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 2 | 6 => 3
def pXS4b73 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 1 | 6 => 2
def pXS4b70inv : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2
def pXS4b71inv : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 1 | 6 => 4
def pXS4b72inv : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 0 | 5 => 3 | 6 => 1
def pXS4b73inv : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 6 | 3 => 3 | 4 => 1 | 5 => 4 | 6 => 0

def permXS4b7 : Fin 4 → Fin 7 → Fin 7
  | 0 => pXS4b70
  | 1 => pXS4b71
  | 2 => pXS4b72
  | 3 => pXS4b73

def permXinvS4b7 : Fin 4 → Fin 7 → Fin 7
  | 0 => pXS4b70inv
  | 1 => pXS4b71inv
  | 2 => pXS4b72inv
  | 3 => pXS4b73inv

def eXS4b7 (i : Fin 4) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXS4b7 i) (permXinvS4b7 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `6`, so an invariant
operation is `6` values. -/
def repS4b7 : Fin 6 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)
  | 5 => (1, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS4b7 : Fin 7 → Fin 7 → Fin 6 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 4)
  | 0, 3 => (1, 8)
  | 0, 4 => (1, 12)
  | 0, 5 => (1, 16)
  | 0, 6 => (1, 20)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (5, 0)
  | 1, 4 => (5, 1)
  | 1, 5 => (5, 2)
  | 1, 6 => (5, 3)
  | 2, 0 => (2, 4)
  | 2, 1 => (4, 4)
  | 2, 2 => (3, 4)
  | 2, 3 => (5, 4)
  | 2, 4 => (5, 5)
  | 2, 5 => (5, 6)
  | 2, 6 => (5, 7)
  | 3, 0 => (2, 8)
  | 3, 1 => (5, 8)
  | 3, 2 => (5, 9)
  | 3, 3 => (3, 8)
  | 3, 4 => (5, 10)
  | 3, 5 => (4, 8)
  | 3, 6 => (5, 11)
  | 4, 0 => (2, 12)
  | 4, 1 => (5, 12)
  | 4, 2 => (5, 13)
  | 4, 3 => (5, 14)
  | 4, 4 => (3, 12)
  | 4, 5 => (5, 15)
  | 4, 6 => (4, 12)
  | 5, 0 => (2, 16)
  | 5, 1 => (5, 16)
  | 5, 2 => (5, 17)
  | 5, 3 => (4, 16)
  | 5, 4 => (5, 18)
  | 5, 5 => (3, 16)
  | 5, 6 => (5, 19)
  | 6, 0 => (2, 20)
  | 6, 1 => (5, 20)
  | 6, 2 => (5, 21)
  | 6, 3 => (5, 22)
  | 6, 4 => (4, 20)
  | 6, 5 => (5, 23)
  | 6, 6 => (3, 20)

/-- The `24` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS4b70 : Fin 24 → Fin 24
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
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 15
  | 16 => 16
  | 17 => 17
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 21
  | 22 => 22
  | _ => 23
def valS4b70 : Fin 1 → Fin 7
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4b71 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4b71 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4b72 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4b72 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4b73 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4b73 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4b74 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4b74 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxS4b75 : Fin 1 → Fin 24
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def decS4b7 (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Fin 6 → Fin 7
  | 0 => valS4b70 a
  | 1 => valS4b71 b
  | 2 => valS4b72 c
  | 3 => valS4b73 d
  | 4 => valS4b74 e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS4b7_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS4b7 (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valS4b70 a
  | 0, 1 => valS4b71 b
  | 0, 2 => pES4b74 (valS4b71 b)
  | 0, 3 => pES4b78 (valS4b71 b)
  | 0, 4 => pES4b712 (valS4b71 b)
  | 0, 5 => pES4b716 (valS4b71 b)
  | 0, 6 => pES4b720 (valS4b71 b)
  | 1, 0 => valS4b72 c
  | 1, 1 => valS4b73 d
  | 1, 2 => valS4b74 e
  | 1, 3 => f
  | 1, 4 => pES4b71 f
  | 1, 5 => pES4b72 f
  | 1, 6 => pES4b73 f
  | 2, 0 => pES4b74 (valS4b72 c)
  | 2, 1 => pES4b74 (valS4b74 e)
  | 2, 2 => pES4b74 (valS4b73 d)
  | 2, 3 => pES4b74 f
  | 2, 4 => pES4b75 f
  | 2, 5 => pES4b76 f
  | 2, 6 => pES4b77 f
  | 3, 0 => pES4b78 (valS4b72 c)
  | 3, 1 => pES4b78 f
  | 3, 2 => pES4b79 f
  | 3, 3 => pES4b78 (valS4b73 d)
  | 3, 4 => pES4b710 f
  | 3, 5 => pES4b78 (valS4b74 e)
  | 3, 6 => pES4b711 f
  | 4, 0 => pES4b712 (valS4b72 c)
  | 4, 1 => pES4b712 f
  | 4, 2 => pES4b713 f
  | 4, 3 => pES4b714 f
  | 4, 4 => pES4b712 (valS4b73 d)
  | 4, 5 => pES4b715 f
  | 4, 6 => pES4b712 (valS4b74 e)
  | 5, 0 => pES4b716 (valS4b72 c)
  | 5, 1 => pES4b716 f
  | 5, 2 => pES4b717 f
  | 5, 3 => pES4b716 (valS4b74 e)
  | 5, 4 => pES4b718 f
  | 5, 5 => pES4b716 (valS4b73 d)
  | 5, 6 => pES4b719 f
  | 6, 0 => pES4b720 (valS4b72 c)
  | 6, 1 => pES4b720 f
  | 6, 2 => pES4b721 f
  | 6, 3 => pES4b722 f
  | 6, 4 => pES4b720 (valS4b74 e)
  | 6, 5 => pES4b723 f
  | 6, 6 => pES4b720 (valS4b73 d)

theorem tabS4b7_eq_transport (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) :
    tabS4b7 a b c d e f = Magma.transport permES4b7 trS4b7 (decS4b7 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `160` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `567` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowS4b70 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 0 0 0 0 4
  | 1 => tabS4b7 0 0 0 0 0 6
  | 2 => tabS4b7 0 0 0 0 1 4
  | 3 => tabS4b7 0 0 0 0 1 6
  | 4 => tabS4b7 0 0 0 0 2 4
  | 5 => tabS4b7 0 0 0 0 2 6
  | 6 => tabS4b7 0 0 0 1 0 4
  | 7 => tabS4b7 0 0 0 1 0 6
  | 8 => tabS4b7 0 0 0 1 1 4
  | 9 => tabS4b7 0 0 0 1 1 6
  | 10 => tabS4b7 0 0 0 1 2 4
  | 11 => tabS4b7 0 0 0 1 2 6
  | _ => tabS4b7 0 0 0 2 0 4
def memRowS4b71 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 0 0 2 0 6
  | 1 => tabS4b7 0 0 0 2 1 4
  | 2 => tabS4b7 0 0 0 2 1 6
  | 3 => tabS4b7 0 0 0 2 2 4
  | 4 => tabS4b7 0 0 0 2 2 6
  | 5 => tabS4b7 0 0 1 0 0 4
  | 6 => tabS4b7 0 0 1 0 0 6
  | 7 => tabS4b7 0 0 1 0 1 4
  | 8 => tabS4b7 0 0 1 0 1 6
  | 9 => tabS4b7 0 0 1 0 2 4
  | 10 => tabS4b7 0 0 1 0 2 6
  | 11 => tabS4b7 0 0 1 1 0 4
  | _ => tabS4b7 0 0 1 1 0 6
def memRowS4b72 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 0 1 1 1 4
  | 1 => tabS4b7 0 0 1 1 1 6
  | 2 => tabS4b7 0 0 1 1 2 4
  | 3 => tabS4b7 0 0 1 1 2 6
  | 4 => tabS4b7 0 0 1 2 0 4
  | 5 => tabS4b7 0 0 1 2 0 6
  | 6 => tabS4b7 0 0 1 2 1 4
  | 7 => tabS4b7 0 0 1 2 1 6
  | 8 => tabS4b7 0 0 1 2 2 4
  | 9 => tabS4b7 0 0 1 2 2 6
  | 10 => tabS4b7 0 0 2 0 0 4
  | 11 => tabS4b7 0 0 2 0 0 6
  | _ => tabS4b7 0 0 2 0 1 4
def memRowS4b73 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 0 2 0 1 6
  | 1 => tabS4b7 0 0 2 0 2 4
  | 2 => tabS4b7 0 0 2 0 2 6
  | 3 => tabS4b7 0 0 2 1 0 4
  | 4 => tabS4b7 0 0 2 1 0 6
  | 5 => tabS4b7 0 0 2 1 1 4
  | 6 => tabS4b7 0 0 2 1 1 6
  | 7 => tabS4b7 0 0 2 1 2 4
  | 8 => tabS4b7 0 0 2 1 2 6
  | 9 => tabS4b7 0 0 2 2 0 4
  | 10 => tabS4b7 0 0 2 2 0 6
  | 11 => tabS4b7 0 0 2 2 1 4
  | _ => tabS4b7 0 0 2 2 1 6
def memRowS4b74 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 0 2 2 2 4
  | 1 => tabS4b7 0 0 2 2 2 6
  | 2 => tabS4b7 0 1 0 0 0 4
  | 3 => tabS4b7 0 1 0 0 0 6
  | 4 => tabS4b7 0 1 0 0 1 4
  | 5 => tabS4b7 0 1 0 0 1 6
  | 6 => tabS4b7 0 1 0 0 2 4
  | 7 => tabS4b7 0 1 0 0 2 6
  | 8 => tabS4b7 0 1 0 1 0 4
  | 9 => tabS4b7 0 1 0 1 0 6
  | 10 => tabS4b7 0 1 0 1 1 4
  | 11 => tabS4b7 0 1 0 1 1 6
  | _ => tabS4b7 0 1 0 1 2 4
def memRowS4b75 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 1 0 1 2 6
  | 1 => tabS4b7 0 1 0 2 0 4
  | 2 => tabS4b7 0 1 0 2 0 6
  | 3 => tabS4b7 0 1 0 2 1 4
  | 4 => tabS4b7 0 1 0 2 1 6
  | 5 => tabS4b7 0 1 0 2 2 4
  | 6 => tabS4b7 0 1 0 2 2 6
  | 7 => tabS4b7 0 1 1 0 0 4
  | 8 => tabS4b7 0 1 1 0 0 6
  | 9 => tabS4b7 0 1 1 0 1 4
  | 10 => tabS4b7 0 1 1 0 1 6
  | 11 => tabS4b7 0 1 1 0 2 4
  | _ => tabS4b7 0 1 1 0 2 6
def memRowS4b76 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 1 1 1 0 4
  | 1 => tabS4b7 0 1 1 1 0 6
  | 2 => tabS4b7 0 1 1 1 1 4
  | 3 => tabS4b7 0 1 1 1 1 6
  | 4 => tabS4b7 0 1 1 1 2 4
  | 5 => tabS4b7 0 1 1 1 2 6
  | 6 => tabS4b7 0 1 1 2 0 4
  | 7 => tabS4b7 0 1 1 2 0 6
  | 8 => tabS4b7 0 1 1 2 1 4
  | 9 => tabS4b7 0 1 1 2 1 6
  | 10 => tabS4b7 0 1 1 2 2 4
  | 11 => tabS4b7 0 1 1 2 2 6
  | _ => tabS4b7 0 1 2 0 0 4
def memRowS4b77 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 1 2 0 0 6
  | 1 => tabS4b7 0 1 2 0 1 4
  | 2 => tabS4b7 0 1 2 0 1 6
  | 3 => tabS4b7 0 1 2 0 2 4
  | 4 => tabS4b7 0 1 2 0 2 6
  | 5 => tabS4b7 0 1 2 1 0 4
  | 6 => tabS4b7 0 1 2 1 0 6
  | 7 => tabS4b7 0 1 2 1 1 4
  | 8 => tabS4b7 0 1 2 1 1 6
  | 9 => tabS4b7 0 1 2 1 2 4
  | 10 => tabS4b7 0 1 2 1 2 6
  | 11 => tabS4b7 0 1 2 2 0 4
  | _ => tabS4b7 0 1 2 2 0 6
def memRowS4b78 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 1 2 2 1 4
  | 1 => tabS4b7 0 1 2 2 1 6
  | 2 => tabS4b7 0 1 2 2 2 4
  | 3 => tabS4b7 0 1 2 2 2 6
  | 4 => tabS4b7 0 2 0 0 0 4
  | 5 => tabS4b7 0 2 0 0 0 6
  | 6 => tabS4b7 0 2 0 0 1 4
  | 7 => tabS4b7 0 2 0 0 1 6
  | 8 => tabS4b7 0 2 0 0 2 4
  | 9 => tabS4b7 0 2 0 0 2 6
  | 10 => tabS4b7 0 2 0 1 0 4
  | 11 => tabS4b7 0 2 0 1 0 6
  | _ => tabS4b7 0 2 0 1 1 4
def memRowS4b79 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 2 0 1 1 6
  | 1 => tabS4b7 0 2 0 1 2 4
  | 2 => tabS4b7 0 2 0 1 2 6
  | 3 => tabS4b7 0 2 0 2 0 4
  | 4 => tabS4b7 0 2 0 2 0 6
  | 5 => tabS4b7 0 2 0 2 1 4
  | 6 => tabS4b7 0 2 0 2 1 6
  | 7 => tabS4b7 0 2 0 2 2 4
  | 8 => tabS4b7 0 2 0 2 2 6
  | 9 => tabS4b7 0 2 1 0 0 4
  | 10 => tabS4b7 0 2 1 0 0 6
  | 11 => tabS4b7 0 2 1 0 1 4
  | _ => tabS4b7 0 2 1 0 1 6
def memRowS4b710 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 2 1 0 2 4
  | 1 => tabS4b7 0 2 1 0 2 6
  | 2 => tabS4b7 0 2 1 1 0 4
  | 3 => tabS4b7 0 2 1 1 0 6
  | 4 => tabS4b7 0 2 1 1 1 4
  | 5 => tabS4b7 0 2 1 1 1 6
  | 6 => tabS4b7 0 2 1 1 2 4
  | 7 => tabS4b7 0 2 1 1 2 6
  | 8 => tabS4b7 0 2 1 2 0 4
  | 9 => tabS4b7 0 2 1 2 0 6
  | 10 => tabS4b7 0 2 1 2 1 4
  | 11 => tabS4b7 0 2 1 2 1 6
  | _ => tabS4b7 0 2 1 2 2 4
def memRowS4b711 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 2 1 2 2 6
  | 1 => tabS4b7 0 2 2 0 0 4
  | 2 => tabS4b7 0 2 2 0 0 6
  | 3 => tabS4b7 0 2 2 0 1 4
  | 4 => tabS4b7 0 2 2 0 1 6
  | 5 => tabS4b7 0 2 2 0 2 4
  | 6 => tabS4b7 0 2 2 0 2 6
  | 7 => tabS4b7 0 2 2 1 1 4
  | 8 => tabS4b7 0 2 2 1 1 6
  | 9 => tabS4b7 0 2 2 1 2 4
  | 10 => tabS4b7 0 2 2 1 2 6
  | 11 => tabS4b7 0 2 2 2 0 4
  | _ => tabS4b7 0 2 2 2 0 6
def memRowS4b712 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4b7 0 2 2 2 1 4
  | 1 => tabS4b7 0 2 2 2 1 6
  | 2 => tabS4b7 0 2 2 2 2 4
  | _ => tabS4b7 0 2 2 2 2 6
def memS4b7 (i : Fin 160) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 13 : Nat) with
  | 0 => memRowS4b70 ⟨i.1 % 13, by omega⟩
  | 1 => memRowS4b71 ⟨i.1 % 13, by omega⟩
  | 2 => memRowS4b72 ⟨i.1 % 13, by omega⟩
  | 3 => memRowS4b73 ⟨i.1 % 13, by omega⟩
  | 4 => memRowS4b74 ⟨i.1 % 13, by omega⟩
  | 5 => memRowS4b75 ⟨i.1 % 13, by omega⟩
  | 6 => memRowS4b76 ⟨i.1 % 13, by omega⟩
  | 7 => memRowS4b77 ⟨i.1 % 13, by omega⟩
  | 8 => memRowS4b78 ⟨i.1 % 13, by omega⟩
  | 9 => memRowS4b79 ⟨i.1 % 13, by omega⟩
  | 10 => memRowS4b710 ⟨i.1 % 13, by omega⟩
  | 11 => memRowS4b711 ⟨i.1 % 13, by omega⟩
  | _ => memRowS4b712 ⟨i.1 % 13, by omega⟩

/-- Which of the `160` members a given invariant tuple is, so that `mem_of_isExactS4b7` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS4b7 : Array Nat := #[
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0, 6, 0, 7, 0, 0, 0, 0,
  8, 0, 9, 0, 0, 0, 0, 10, 0, 11, 0, 0, 0, 0, 12, 0, 13, 0, 0, 0, 0, 14, 0, 15, 0, 0, 0, 0, 16,
  0, 17, 0, 0, 0, 0, 18, 0, 19, 0, 0, 0, 0, 20, 0, 21, 0, 0, 0, 0, 22, 0, 23, 0, 0, 0, 0, 24, 0,
  25, 0, 0, 0, 0, 26, 0, 27, 0, 0, 0, 0, 28, 0, 29, 0, 0, 0, 0, 30, 0, 31, 0, 0, 0, 0, 32, 0, 33,
  0, 0, 0, 0, 34, 0, 35, 0, 0, 0, 0, 36, 0, 37, 0, 0, 0, 0, 38, 0, 39, 0, 0, 0, 0, 40, 0, 41, 0,
  0, 0, 0, 42, 0, 43, 0, 0, 0, 0, 44, 0, 45, 0, 0, 0, 0, 46, 0, 47, 0, 0, 0, 0, 48, 0, 49, 0, 0,
  0, 0, 50, 0, 51, 0, 0, 0, 0, 52, 0, 53, 0, 0, 0, 0, 54, 0, 55, 0, 0, 0, 0, 56, 0, 57, 0, 0, 0,
  0, 58, 0, 59, 0, 0, 0, 0, 60, 0, 61, 0, 0, 0, 0, 62, 0, 63, 0, 0, 0, 0, 64, 0, 65, 0, 0, 0, 0,
  66, 0, 67, 0, 0, 0, 0, 68, 0, 69, 0, 0, 0, 0, 70, 0, 71, 0, 0, 0, 0, 72, 0, 73, 0, 0, 0, 0, 74,
  0, 75, 0, 0, 0, 0, 76, 0, 77, 0, 0, 0, 0, 78, 0, 79, 0, 0, 0, 0, 80, 0, 81, 0, 0, 0, 0, 82, 0,
  83, 0, 0, 0, 0, 84, 0, 85, 0, 0, 0, 0, 86, 0, 87, 0, 0, 0, 0, 88, 0, 89, 0, 0, 0, 0, 90, 0, 91,
  0, 0, 0, 0, 92, 0, 93, 0, 0, 0, 0, 94, 0, 95, 0, 0, 0, 0, 96, 0, 97, 0, 0, 0, 0, 98, 0, 99, 0,
  0, 0, 0, 100, 0, 101, 0, 0, 0, 0, 102, 0, 103, 0, 0, 0, 0, 104, 0, 105, 0, 0, 0, 0, 106, 0,
  107, 0, 0, 0, 0, 108, 0, 109, 0, 0, 0, 0, 110, 0, 111, 0, 0, 0, 0, 112, 0, 113, 0, 0, 0, 0,
  114, 0, 115, 0, 0, 0, 0, 116, 0, 117, 0, 0, 0, 0, 118, 0, 119, 0, 0, 0, 0, 120, 0, 121, 0, 0,
  0, 0, 122, 0, 123, 0, 0, 0, 0, 124, 0, 125, 0, 0, 0, 0, 126, 0, 127, 0, 0, 0, 0, 128, 0, 129,
  0, 0, 0, 0, 130, 0, 131, 0, 0, 0, 0, 132, 0, 133, 0, 0, 0, 0, 134, 0, 135, 0, 0, 0, 0, 136, 0,
  137, 0, 0, 0, 0, 138, 0, 139, 0, 0, 0, 0, 140, 0, 141, 0, 0, 0, 0, 142, 0, 143, 0, 0, 0, 0,
  144, 0, 145, 0, 0, 0, 0, 146, 0, 147, 0, 0, 0, 0, 148, 0, 149, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  150, 0, 151, 0, 0, 0, 0, 152, 0, 153, 0, 0, 0, 0, 154, 0, 155, 0, 0, 0, 0, 156, 0, 157, 0, 0,
  0, 0, 158, 0, 159]

/-- The arguments as one mixed-radix index, which is how `rankArrS4b7` is addressed. -/
def encTS4b7 (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Nat :=
  a.1 * 567 +
    b.1 * 189 +
    c.1 * 63 +
    d.1 * 21 +
    e.1 * 7 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS4b7 (a : Fin 1) (b c d e : Fin 3) (f : Fin 7) : Fin 160 :=
  ⟨min (rankArrS4b7.getD (encTS4b7 a b c d e f) 0) 159, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS4b7 (i : Fin 160) : Magma (Fin 7) := Magma.mk (memS4b7 i)

theorem exactS4b7_isEndo (i : Fin 160) (j : Fin 24) : (exactS4b7 i).IsEndo ⇑(eES4b7 j) := by
  simp only [eES4b7, coe_permOf]; revert i j; native_decide

theorem exactS4b7_not_isEndo (i : Fin 160) (j : Fin 4) : ¬ (exactS4b7 i).IsEndo ⇑(eXS4b7 j) := by
  simp only [eXS4b7, coe_permOf]; revert i j; native_decide

/-- `rankS4b7` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS4b7` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS4b7 (a : Fin 1) (b c d e : Fin 3) (f : Fin 7)
    (h : Magma.isExact (tabS4b7 a b c d e f) permES4b7 permXS4b7 = true) :
    memS4b7 (rankS4b7 a b c d e f) = tabS4b7 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `160`
listed members. -/
theorem mem_of_isExactS4b7 (a : Fin 1) (b c d e : Fin 3) (f : Fin 7)
    (h : Magma.isExact (tabS4b7 a b c d e f) permES4b7 permXS4b7 = true) :
    ∃ i, memS4b7 i = tabS4b7 a b c d e f :=
  ⟨_, mem_rankS4b7 a b c d e f h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS4b7`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS4b7` turns that into a member index. -/
theorem exists_exactS4b7 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eES4b7 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS4b7 i)) : ∃ i, exactS4b7 i = M := by
  simp only [eES4b7, coe_permOf] at hE
  simp only [eXS4b7, coe_permOf] at hX
  have hop : M.op = Magma.transport permES4b7 trS4b7 (fun i ↦ M.op (repS4b7 i).1 (repS4b7 i).2) :=
    Magma.op_eq_transport (rep := repS4b7) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES4b7) (idx := stabIdxS4b70) (a := (repS4b7 0).1) (b := (repS4b7 0).2)
    (val := valS4b70) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES4b7) (idx := stabIdxS4b71) (a := (repS4b7 1).1) (b := (repS4b7 1).2)
    (val := valS4b71) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES4b7) (idx := stabIdxS4b72) (a := (repS4b7 2).1) (b := (repS4b7 2).2)
    (val := valS4b72) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES4b7) (idx := stabIdxS4b73) (a := (repS4b7 3).1) (b := (repS4b7 3).2)
    (val := valS4b73) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES4b7) (idx := stabIdxS4b74) (a := (repS4b7 4).1) (b := (repS4b7 4).2)
    (val := valS4b74) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permES4b7) (idx := stabIdxS4b75) (a := (repS4b7 5).1) (b := (repS4b7 5).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decS4b7 a b c d e f = fun i ↦ M.op (repS4b7 i).1 (repS4b7 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabS4b7 a b c d e f = M.op := by
    rw [tabS4b7_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS4b7 a b c d e f) permES4b7 permXS4b7 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS4b7 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`24` group of `Magma.permES4b7`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS4b7 {L L' : Law.NatMagmaLaw} {i : Fin 160}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactS4b7 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactS4b7 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS4b7 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS4b7
    (fun k ↦ (Magma.exactS4b7_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS4b7_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
