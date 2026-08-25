import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S4a7` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 2)(3 4)(5 6), (0 2)(3 6)(4 5), (0 3)(2 5)(4 6)⟩` -/

/-- The `24` elements of the group: `()`, `(3 4 5 6)`, `(3 5)(4 6)`, `(3 6 5 4)`, `(0 2)(4 6)`, `(0
2)(3 4)(5 6)`, `(0 2)(3 5)`, `(0 2)(3 6)(4 5)`, `(0 3)(2 5)(4 6)`, `(0 3 2 5)`, `(0 3 4)(2 5 6)`,
`(0 3 6)(2 5 4)`, `(0 4 3)(2 6 5)`, `(0 4 5)(2 6 3)`, `(0 4 2 6)`, `(0 4)(2 6)(3 5)`, `(0 5 2 3)`,
`(0 5)(2 3)(4 6)`, `(0 5 6)(2 3 4)`, `(0 5 4)(2 3 6)`, `(0 6 3)(2 4 5)`, `(0 6 5)(2 4 3)`, `(0 6 2
4)`, `(0 6)(2 4)(3 5)`. -/
def pES4a70 : Fin 7 → Fin 7 := id
def pES4a71 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 3
def pES4a72 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4
def pES4a73 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 3 | 5 => 4 | 6 => 5
def pES4a74 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 6 | 5 => 5 | 6 => 4
def pES4a75 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pES4a76 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 6
def pES4a77 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 3
def pES4a78 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 0 | 4 => 6 | 5 => 2 | 6 => 4
def pES4a79 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 2 | 4 => 4 | 5 => 0 | 6 => 6
def pES4a710 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 2
def pES4a711 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 4 | 6 => 0
def pES4a712 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 0 | 4 => 3 | 5 => 2 | 6 => 5
def pES4a713 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 0 | 6 => 3
def pES4a714 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 0
def pES4a715 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 5 | 4 => 0 | 5 => 3 | 6 => 2
def pES4a716 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 2 | 6 => 6
def pES4a717 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 0 | 6 => 4
def pES4a718 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 0
def pES4a719 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 6 | 4 => 0 | 5 => 4 | 6 => 2
def pES4a720 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 2 | 6 => 3
def pES4a721 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 0 | 6 => 5
def pES4a722 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 2
def pES4a723 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 0

def permES4a7 : Fin 24 → Fin 7 → Fin 7
  | 0 => pES4a70
  | 1 => pES4a71
  | 2 => pES4a72
  | 3 => pES4a73
  | 4 => pES4a74
  | 5 => pES4a75
  | 6 => pES4a76
  | 7 => pES4a77
  | 8 => pES4a78
  | 9 => pES4a79
  | 10 => pES4a710
  | 11 => pES4a711
  | 12 => pES4a712
  | 13 => pES4a713
  | 14 => pES4a714
  | 15 => pES4a715
  | 16 => pES4a716
  | 17 => pES4a717
  | 18 => pES4a718
  | 19 => pES4a719
  | 20 => pES4a720
  | 21 => pES4a721
  | 22 => pES4a722
  | _ => pES4a723

def permEinvS4a7 : Fin 24 → Fin 7 → Fin 7
  | 0 => pES4a70
  | 1 => pES4a73
  | 2 => pES4a72
  | 3 => pES4a71
  | 4 => pES4a74
  | 5 => pES4a75
  | 6 => pES4a76
  | 7 => pES4a77
  | 8 => pES4a78
  | 9 => pES4a716
  | 10 => pES4a712
  | 11 => pES4a720
  | 12 => pES4a710
  | 13 => pES4a719
  | 14 => pES4a722
  | 15 => pES4a715
  | 16 => pES4a79
  | 17 => pES4a717
  | 18 => pES4a721
  | 19 => pES4a713
  | 20 => pES4a711
  | 21 => pES4a718
  | 22 => pES4a714
  | _ => pES4a723

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES4a7 (i : Fin 24) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permES4a7 i) (permEinvS4a7 i) (by revert i; decide)

/-- The `3` permutations that must *not* be automorphisms: `(3 4)(5 6)`, `(0 4 6)(2 3 5)`, `(0 5 4 3
2 6)`. Every subgroup properly containing the group above contains one of them, so a magma admitting
the group and not these has that group as its automorphism group exactly. -/
def pXS4a70 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pXS4a71 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 6 | 5 => 2 | 6 => 0
def pXS4a72 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 6 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 0
def pXS4a70inv : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pXS4a71inv : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 3 | 6 => 4
def pXS4a72inv : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 0 | 6 => 2

def permXS4a7 : Fin 3 → Fin 7 → Fin 7
  | 0 => pXS4a70
  | 1 => pXS4a71
  | 2 => pXS4a72

def permXinvS4a7 : Fin 3 → Fin 7 → Fin 7
  | 0 => pXS4a70inv
  | 1 => pXS4a71inv
  | 2 => pXS4a72inv

def eXS4a7 (i : Fin 3) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXS4a7 i) (permXinvS4a7 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `6`, so an invariant
operation is `6` values. -/
def repS4a7 : Fin 6 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)
  | 4 => (1, 0)
  | 5 => (1, 1)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS4a7 : Fin 7 → Fin 7 → Fin 6 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (3, 1)
  | 0, 5 => (3, 2)
  | 0, 6 => (3, 3)
  | 1, 0 => (4, 0)
  | 1, 1 => (5, 0)
  | 1, 2 => (4, 4)
  | 1, 3 => (4, 8)
  | 1, 4 => (4, 12)
  | 1, 5 => (4, 16)
  | 1, 6 => (4, 20)
  | 2, 0 => (2, 4)
  | 2, 1 => (1, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 4)
  | 2, 4 => (3, 5)
  | 2, 5 => (3, 6)
  | 2, 6 => (3, 7)
  | 3, 0 => (3, 8)
  | 3, 1 => (1, 8)
  | 3, 2 => (3, 9)
  | 3, 3 => (0, 8)
  | 3, 4 => (3, 10)
  | 3, 5 => (2, 8)
  | 3, 6 => (3, 11)
  | 4, 0 => (3, 12)
  | 4, 1 => (1, 12)
  | 4, 2 => (3, 13)
  | 4, 3 => (3, 14)
  | 4, 4 => (0, 12)
  | 4, 5 => (3, 15)
  | 4, 6 => (2, 12)
  | 5, 0 => (3, 16)
  | 5, 1 => (1, 16)
  | 5, 2 => (3, 17)
  | 5, 3 => (2, 16)
  | 5, 4 => (3, 18)
  | 5, 5 => (0, 16)
  | 5, 6 => (3, 19)
  | 6, 0 => (3, 20)
  | 6, 1 => (1, 20)
  | 6, 2 => (3, 21)
  | 6, 3 => (3, 22)
  | 6, 4 => (2, 20)
  | 6, 5 => (3, 23)
  | 6, 6 => (0, 20)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4a70 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4a70 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4a71 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4a71 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4a72 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4a72 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxS4a73 : Fin 1 → Fin 24
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS4a74 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4a74 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `24` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `1`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS4a75 : Fin 24 → Fin 24
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
def valS4a75 : Fin 1 → Fin 7
  | 0 => 1

/-- The `6` orbit values named by the family's arguments. -/
def decS4a7 (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1) : Fin 6 → Fin 7
  | 0 => valS4a70 a
  | 1 => valS4a71 b
  | 2 => valS4a72 c
  | 3 => d
  | 4 => valS4a74 e
  | 5 => valS4a75 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS4a7_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS4a7 (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valS4a70 a
  | 0, 1 => valS4a71 b
  | 0, 2 => valS4a72 c
  | 0, 3 => d
  | 0, 4 => pES4a71 d
  | 0, 5 => pES4a72 d
  | 0, 6 => pES4a73 d
  | 1, 0 => valS4a74 e
  | 1, 1 => valS4a75 f
  | 1, 2 => pES4a74 (valS4a74 e)
  | 1, 3 => pES4a78 (valS4a74 e)
  | 1, 4 => pES4a712 (valS4a74 e)
  | 1, 5 => pES4a716 (valS4a74 e)
  | 1, 6 => pES4a720 (valS4a74 e)
  | 2, 0 => pES4a74 (valS4a72 c)
  | 2, 1 => pES4a74 (valS4a71 b)
  | 2, 2 => pES4a74 (valS4a70 a)
  | 2, 3 => pES4a74 d
  | 2, 4 => pES4a75 d
  | 2, 5 => pES4a76 d
  | 2, 6 => pES4a77 d
  | 3, 0 => pES4a78 d
  | 3, 1 => pES4a78 (valS4a71 b)
  | 3, 2 => pES4a79 d
  | 3, 3 => pES4a78 (valS4a70 a)
  | 3, 4 => pES4a710 d
  | 3, 5 => pES4a78 (valS4a72 c)
  | 3, 6 => pES4a711 d
  | 4, 0 => pES4a712 d
  | 4, 1 => pES4a712 (valS4a71 b)
  | 4, 2 => pES4a713 d
  | 4, 3 => pES4a714 d
  | 4, 4 => pES4a712 (valS4a70 a)
  | 4, 5 => pES4a715 d
  | 4, 6 => pES4a712 (valS4a72 c)
  | 5, 0 => pES4a716 d
  | 5, 1 => pES4a716 (valS4a71 b)
  | 5, 2 => pES4a717 d
  | 5, 3 => pES4a716 (valS4a72 c)
  | 5, 4 => pES4a718 d
  | 5, 5 => pES4a716 (valS4a70 a)
  | 5, 6 => pES4a719 d
  | 6, 0 => pES4a720 d
  | 6, 1 => pES4a720 (valS4a71 b)
  | 6, 2 => pES4a721 d
  | 6, 3 => pES4a722 d
  | 6, 4 => pES4a720 (valS4a72 c)
  | 6, 5 => pES4a723 d
  | 6, 6 => pES4a720 (valS4a70 a)

theorem tabS4a7_eq_transport (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1) :
    tabS4a7 a b c d e f = Magma.transport permES4a7 trS4a7 (decS4a7 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `162` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `567` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowS4a70 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 0 0 0 4 0 0
  | 1 => tabS4a7 0 0 0 4 1 0
  | 2 => tabS4a7 0 0 0 4 2 0
  | 3 => tabS4a7 0 0 0 6 0 0
  | 4 => tabS4a7 0 0 0 6 1 0
  | 5 => tabS4a7 0 0 0 6 2 0
  | 6 => tabS4a7 0 0 1 4 0 0
  | 7 => tabS4a7 0 0 1 4 1 0
  | 8 => tabS4a7 0 0 1 4 2 0
  | 9 => tabS4a7 0 0 1 6 0 0
  | 10 => tabS4a7 0 0 1 6 1 0
  | 11 => tabS4a7 0 0 1 6 2 0
  | _ => tabS4a7 0 0 2 4 0 0
def memRowS4a71 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 0 0 2 4 1 0
  | 1 => tabS4a7 0 0 2 4 2 0
  | 2 => tabS4a7 0 0 2 6 0 0
  | 3 => tabS4a7 0 0 2 6 1 0
  | 4 => tabS4a7 0 0 2 6 2 0
  | 5 => tabS4a7 0 1 0 4 0 0
  | 6 => tabS4a7 0 1 0 4 1 0
  | 7 => tabS4a7 0 1 0 4 2 0
  | 8 => tabS4a7 0 1 0 6 0 0
  | 9 => tabS4a7 0 1 0 6 1 0
  | 10 => tabS4a7 0 1 0 6 2 0
  | 11 => tabS4a7 0 1 1 4 0 0
  | _ => tabS4a7 0 1 1 4 1 0
def memRowS4a72 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 0 1 1 4 2 0
  | 1 => tabS4a7 0 1 1 6 0 0
  | 2 => tabS4a7 0 1 1 6 1 0
  | 3 => tabS4a7 0 1 1 6 2 0
  | 4 => tabS4a7 0 1 2 4 0 0
  | 5 => tabS4a7 0 1 2 4 1 0
  | 6 => tabS4a7 0 1 2 4 2 0
  | 7 => tabS4a7 0 1 2 6 0 0
  | 8 => tabS4a7 0 1 2 6 1 0
  | 9 => tabS4a7 0 1 2 6 2 0
  | 10 => tabS4a7 0 2 0 4 0 0
  | 11 => tabS4a7 0 2 0 4 1 0
  | _ => tabS4a7 0 2 0 4 2 0
def memRowS4a73 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 0 2 0 6 0 0
  | 1 => tabS4a7 0 2 0 6 1 0
  | 2 => tabS4a7 0 2 0 6 2 0
  | 3 => tabS4a7 0 2 1 4 0 0
  | 4 => tabS4a7 0 2 1 4 1 0
  | 5 => tabS4a7 0 2 1 4 2 0
  | 6 => tabS4a7 0 2 1 6 0 0
  | 7 => tabS4a7 0 2 1 6 1 0
  | 8 => tabS4a7 0 2 1 6 2 0
  | 9 => tabS4a7 0 2 2 4 0 0
  | 10 => tabS4a7 0 2 2 4 1 0
  | 11 => tabS4a7 0 2 2 4 2 0
  | _ => tabS4a7 0 2 2 6 0 0
def memRowS4a74 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 0 2 2 6 1 0
  | 1 => tabS4a7 0 2 2 6 2 0
  | 2 => tabS4a7 1 0 0 4 0 0
  | 3 => tabS4a7 1 0 0 4 1 0
  | 4 => tabS4a7 1 0 0 4 2 0
  | 5 => tabS4a7 1 0 0 6 0 0
  | 6 => tabS4a7 1 0 0 6 1 0
  | 7 => tabS4a7 1 0 0 6 2 0
  | 8 => tabS4a7 1 0 1 4 0 0
  | 9 => tabS4a7 1 0 1 4 1 0
  | 10 => tabS4a7 1 0 1 4 2 0
  | 11 => tabS4a7 1 0 1 6 0 0
  | _ => tabS4a7 1 0 1 6 1 0
def memRowS4a75 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 1 0 1 6 2 0
  | 1 => tabS4a7 1 0 2 4 0 0
  | 2 => tabS4a7 1 0 2 4 1 0
  | 3 => tabS4a7 1 0 2 4 2 0
  | 4 => tabS4a7 1 0 2 6 0 0
  | 5 => tabS4a7 1 0 2 6 1 0
  | 6 => tabS4a7 1 0 2 6 2 0
  | 7 => tabS4a7 1 1 0 4 0 0
  | 8 => tabS4a7 1 1 0 4 1 0
  | 9 => tabS4a7 1 1 0 4 2 0
  | 10 => tabS4a7 1 1 0 6 0 0
  | 11 => tabS4a7 1 1 0 6 1 0
  | _ => tabS4a7 1 1 0 6 2 0
def memRowS4a76 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 1 1 1 4 0 0
  | 1 => tabS4a7 1 1 1 4 1 0
  | 2 => tabS4a7 1 1 1 4 2 0
  | 3 => tabS4a7 1 1 1 6 0 0
  | 4 => tabS4a7 1 1 1 6 1 0
  | 5 => tabS4a7 1 1 1 6 2 0
  | 6 => tabS4a7 1 1 2 4 0 0
  | 7 => tabS4a7 1 1 2 4 1 0
  | 8 => tabS4a7 1 1 2 4 2 0
  | 9 => tabS4a7 1 1 2 6 0 0
  | 10 => tabS4a7 1 1 2 6 1 0
  | 11 => tabS4a7 1 1 2 6 2 0
  | _ => tabS4a7 1 2 0 4 0 0
def memRowS4a77 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 1 2 0 4 1 0
  | 1 => tabS4a7 1 2 0 4 2 0
  | 2 => tabS4a7 1 2 0 6 0 0
  | 3 => tabS4a7 1 2 0 6 1 0
  | 4 => tabS4a7 1 2 0 6 2 0
  | 5 => tabS4a7 1 2 1 4 0 0
  | 6 => tabS4a7 1 2 1 4 1 0
  | 7 => tabS4a7 1 2 1 4 2 0
  | 8 => tabS4a7 1 2 1 6 0 0
  | 9 => tabS4a7 1 2 1 6 1 0
  | 10 => tabS4a7 1 2 1 6 2 0
  | 11 => tabS4a7 1 2 2 4 0 0
  | _ => tabS4a7 1 2 2 4 1 0
def memRowS4a78 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 1 2 2 4 2 0
  | 1 => tabS4a7 1 2 2 6 0 0
  | 2 => tabS4a7 1 2 2 6 1 0
  | 3 => tabS4a7 1 2 2 6 2 0
  | 4 => tabS4a7 2 0 0 4 0 0
  | 5 => tabS4a7 2 0 0 4 1 0
  | 6 => tabS4a7 2 0 0 4 2 0
  | 7 => tabS4a7 2 0 0 6 0 0
  | 8 => tabS4a7 2 0 0 6 1 0
  | 9 => tabS4a7 2 0 0 6 2 0
  | 10 => tabS4a7 2 0 1 4 0 0
  | 11 => tabS4a7 2 0 1 4 1 0
  | _ => tabS4a7 2 0 1 4 2 0
def memRowS4a79 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 2 0 1 6 0 0
  | 1 => tabS4a7 2 0 1 6 1 0
  | 2 => tabS4a7 2 0 1 6 2 0
  | 3 => tabS4a7 2 0 2 4 0 0
  | 4 => tabS4a7 2 0 2 4 1 0
  | 5 => tabS4a7 2 0 2 4 2 0
  | 6 => tabS4a7 2 0 2 6 0 0
  | 7 => tabS4a7 2 0 2 6 1 0
  | 8 => tabS4a7 2 0 2 6 2 0
  | 9 => tabS4a7 2 1 0 4 0 0
  | 10 => tabS4a7 2 1 0 4 1 0
  | 11 => tabS4a7 2 1 0 4 2 0
  | _ => tabS4a7 2 1 0 6 0 0
def memRowS4a710 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 2 1 0 6 1 0
  | 1 => tabS4a7 2 1 0 6 2 0
  | 2 => tabS4a7 2 1 1 4 0 0
  | 3 => tabS4a7 2 1 1 4 1 0
  | 4 => tabS4a7 2 1 1 4 2 0
  | 5 => tabS4a7 2 1 1 6 0 0
  | 6 => tabS4a7 2 1 1 6 1 0
  | 7 => tabS4a7 2 1 1 6 2 0
  | 8 => tabS4a7 2 1 2 4 0 0
  | 9 => tabS4a7 2 1 2 4 1 0
  | 10 => tabS4a7 2 1 2 4 2 0
  | 11 => tabS4a7 2 1 2 6 0 0
  | _ => tabS4a7 2 1 2 6 1 0
def memRowS4a711 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 2 1 2 6 2 0
  | 1 => tabS4a7 2 2 0 4 0 0
  | 2 => tabS4a7 2 2 0 4 1 0
  | 3 => tabS4a7 2 2 0 4 2 0
  | 4 => tabS4a7 2 2 0 6 0 0
  | 5 => tabS4a7 2 2 0 6 1 0
  | 6 => tabS4a7 2 2 0 6 2 0
  | 7 => tabS4a7 2 2 1 4 0 0
  | 8 => tabS4a7 2 2 1 4 1 0
  | 9 => tabS4a7 2 2 1 4 2 0
  | 10 => tabS4a7 2 2 1 6 0 0
  | 11 => tabS4a7 2 2 1 6 1 0
  | _ => tabS4a7 2 2 1 6 2 0
def memRowS4a712 : Fin 13 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS4a7 2 2 2 4 0 0
  | 1 => tabS4a7 2 2 2 4 1 0
  | 2 => tabS4a7 2 2 2 4 2 0
  | 3 => tabS4a7 2 2 2 6 0 0
  | 4 => tabS4a7 2 2 2 6 1 0
  | _ => tabS4a7 2 2 2 6 2 0
def memS4a7 (i : Fin 162) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 13 : Nat) with
  | 0 => memRowS4a70 ⟨i.1 % 13, by omega⟩
  | 1 => memRowS4a71 ⟨i.1 % 13, by omega⟩
  | 2 => memRowS4a72 ⟨i.1 % 13, by omega⟩
  | 3 => memRowS4a73 ⟨i.1 % 13, by omega⟩
  | 4 => memRowS4a74 ⟨i.1 % 13, by omega⟩
  | 5 => memRowS4a75 ⟨i.1 % 13, by omega⟩
  | 6 => memRowS4a76 ⟨i.1 % 13, by omega⟩
  | 7 => memRowS4a77 ⟨i.1 % 13, by omega⟩
  | 8 => memRowS4a78 ⟨i.1 % 13, by omega⟩
  | 9 => memRowS4a79 ⟨i.1 % 13, by omega⟩
  | 10 => memRowS4a710 ⟨i.1 % 13, by omega⟩
  | 11 => memRowS4a711 ⟨i.1 % 13, by omega⟩
  | _ => memRowS4a712 ⟨i.1 % 13, by omega⟩

/-- Which of the `162` members a given invariant tuple is, so that `mem_of_isExactS4a7` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS4a7 : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 6, 7, 8, 0, 0, 0, 9, 10, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 14, 0, 0, 0, 15,
  16, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 20, 0, 0, 0, 21, 22, 23, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 24, 25, 26, 0, 0, 0, 27, 28, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 31,
  32, 0, 0, 0, 33, 34, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 37, 38, 0, 0, 0, 39, 40, 41,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 43, 44, 0, 0, 0, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 48, 49, 50, 0, 0, 0, 51, 52, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 55, 56, 0, 0,
  0, 57, 58, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 61, 62, 0, 0, 0, 63, 64, 65, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 69, 70, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  72, 73, 74, 0, 0, 0, 75, 76, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 79, 80, 0, 0, 0, 81,
  82, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 85, 86, 0, 0, 0, 87, 88, 89, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 90, 91, 92, 0, 0, 0, 93, 94, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 97,
  98, 0, 0, 0, 99, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, 103, 104, 0, 0, 0, 105,
  106, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108, 109, 110, 0, 0, 0, 111, 112, 113, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 114, 115, 116, 0, 0, 0, 117, 118, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 120, 121, 122, 0, 0, 0, 123, 124, 125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 127, 128,
  0, 0, 0, 129, 130, 131, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132, 133, 134, 0, 0, 0, 135, 136,
  137, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 138, 139, 140, 0, 0, 0, 141, 142, 143, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 144, 145, 146, 0, 0, 0, 147, 148, 149, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  150, 151, 152, 0, 0, 0, 153, 154, 155, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 157, 158, 0, 0,
  0, 159, 160, 161]

/-- The arguments as one mixed-radix index, which is how `rankArrS4a7` is addressed. -/
def encTS4a7 (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1) : Nat :=
  a.1 * 189 +
    b.1 * 63 +
    c.1 * 21 +
    d.1 * 3 +
    e.1 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS4a7 (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1) : Fin 162 :=
  ⟨min (rankArrS4a7.getD (encTS4a7 a b c d e f) 0) 161, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS4a7 (i : Fin 162) : Magma (Fin 7) := Magma.mk (memS4a7 i)

theorem exactS4a7_isEndo (i : Fin 162) (j : Fin 24) : (exactS4a7 i).IsEndo ⇑(eES4a7 j) := by
  simp only [eES4a7, coe_permOf]; revert i j; native_decide

theorem exactS4a7_not_isEndo (i : Fin 162) (j : Fin 3) : ¬ (exactS4a7 i).IsEndo ⇑(eXS4a7 j) := by
  simp only [eXS4a7, coe_permOf]; revert i j; native_decide

/-- `rankS4a7` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS4a7` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS4a7 (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1)
    (h : Magma.isExact (tabS4a7 a b c d e f) permES4a7 permXS4a7 = true) :
    memS4a7 (rankS4a7 a b c d e f) = tabS4a7 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `162`
listed members. -/
theorem mem_of_isExactS4a7 (a b c : Fin 3) (d : Fin 7) (e : Fin 3) (f : Fin 1)
    (h : Magma.isExact (tabS4a7 a b c d e f) permES4a7 permXS4a7 = true) :
    ∃ i, memS4a7 i = tabS4a7 a b c d e f :=
  ⟨_, mem_rankS4a7 a b c d e f h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS4a7`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS4a7` turns that into a member index. -/
theorem exists_exactS4a7 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eES4a7 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS4a7 i)) : ∃ i, exactS4a7 i = M := by
  simp only [eES4a7, coe_permOf] at hE
  simp only [eXS4a7, coe_permOf] at hX
  have hop : M.op = Magma.transport permES4a7 trS4a7 (fun i ↦ M.op (repS4a7 i).1 (repS4a7 i).2) :=
    Magma.op_eq_transport (rep := repS4a7) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES4a7) (idx := stabIdxS4a70) (a := (repS4a7 0).1) (b := (repS4a7 0).2)
    (val := valS4a70) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES4a7) (idx := stabIdxS4a71) (a := (repS4a7 1).1) (b := (repS4a7 1).2)
    (val := valS4a71) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES4a7) (idx := stabIdxS4a72) (a := (repS4a7 2).1) (b := (repS4a7 2).2)
    (val := valS4a72) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES4a7) (idx := stabIdxS4a73) (a := (repS4a7 3).1) (b := (repS4a7 3).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES4a7) (idx := stabIdxS4a74) (a := (repS4a7 4).1) (b := (repS4a7 4).2)
    (val := valS4a74) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permES4a7) (idx := stabIdxS4a75) (a := (repS4a7 5).1) (b := (repS4a7 5).2)
    (val := valS4a75) hE (by decide) (by decide)
  have hdec : decS4a7 a b c d e f = fun i ↦ M.op (repS4a7 i).1 (repS4a7 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabS4a7 a b c d e f = M.op := by
    rw [tabS4a7_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS4a7 a b c d e f) permES4a7 permXS4a7 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS4a7 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`24` group of `Magma.permES4a7`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS4a7 {L L' : Law.NatMagmaLaw} {i : Fin 162}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactS4a7 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactS4a7 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS4a7 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS4a7
    (fun k ↦ (Magma.exactS4a7_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS4a7_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
