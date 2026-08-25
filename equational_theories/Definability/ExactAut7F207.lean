import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `F207` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`20` group `⟨(0 1)(3 5 4 6), (0 1)(2 3 4 6)⟩` -/

/-- The `20` elements of the group: `()`, `(3 4)(5 6)`, `(2 3)(4 5)`, `(2 3 5 6 4)`, `(2 4 6 5 3)`,
`(2 4)(3 6)`, `(2 5)(4 6)`, `(2 5 4 3 6)`, `(2 6 3 4 5)`, `(2 6)(3 5)`, `(0 1)(3 5 4 6)`, `(0 1)(3 6
4 5)`, `(0 1)(2 3 4 6)`, `(0 1)(2 3 6 5)`, `(0 1)(2 4 5 6)`, `(0 1)(2 4 3 5)`, `(0 1)(2 5 6 3)`, `(0
1)(2 5 3 4)`, `(0 1)(2 6 4 3)`, `(0 1)(2 6 5 4)`. -/
def pEF2070 : Fin 7 → Fin 7 := id
def pEF2071 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pEF2072 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6
def pEF2073 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 2 | 5 => 6 | 6 => 4
def pEF2074 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 6 | 5 => 3 | 6 => 5
def pEF2075 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 6 | 4 => 2 | 5 => 5 | 6 => 3
def pEF2076 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 4
def pEF2077 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 6 | 4 => 3 | 5 => 4 | 6 => 2
def pEF2078 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 4 | 4 => 5 | 5 => 2 | 6 => 3
def pEF2079 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 2
def pEF20710 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 4 | 6 => 3
def pEF20711 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 3 | 6 => 4
def pEF20712 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 6 | 5 => 5 | 6 => 2
def pEF20713 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 6 | 4 => 4 | 5 => 2 | 6 => 5
def pEF20714 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 2
def pEF20715 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2 | 6 => 6
def pEF20716 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 3
def pEF20717 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3 | 6 => 6
def pEF20718 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 6 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 4
def pEF20719 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 6 | 3 => 3 | 4 => 2 | 5 => 4 | 6 => 5

def permEF207 : Fin 20 → Fin 7 → Fin 7
  | 0 => pEF2070
  | 1 => pEF2071
  | 2 => pEF2072
  | 3 => pEF2073
  | 4 => pEF2074
  | 5 => pEF2075
  | 6 => pEF2076
  | 7 => pEF2077
  | 8 => pEF2078
  | 9 => pEF2079
  | 10 => pEF20710
  | 11 => pEF20711
  | 12 => pEF20712
  | 13 => pEF20713
  | 14 => pEF20714
  | 15 => pEF20715
  | 16 => pEF20716
  | 17 => pEF20717
  | 18 => pEF20718
  | _ => pEF20719

def permEinvF207 : Fin 20 → Fin 7 → Fin 7
  | 0 => pEF2070
  | 1 => pEF2071
  | 2 => pEF2072
  | 3 => pEF2074
  | 4 => pEF2073
  | 5 => pEF2075
  | 6 => pEF2076
  | 7 => pEF2078
  | 8 => pEF2077
  | 9 => pEF2079
  | 10 => pEF20711
  | 11 => pEF20710
  | 12 => pEF20718
  | 13 => pEF20716
  | 14 => pEF20719
  | 15 => pEF20717
  | 16 => pEF20713
  | 17 => pEF20715
  | 18 => pEF20712
  | _ => pEF20714

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEF207 (i : Fin 20) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permEF207 i) (permEinvF207 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(3 6 4 5)`, `(2 4 3)`. Every subgroup
properly containing the group above contains one of them, so a magma admitting the group and not
these has that group as its automorphism group exactly. -/
def pXF2070 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 3 | 6 => 4
def pXF2071 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6
def pXF2070inv : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 4 | 6 => 3
def pXF2071inv : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6

def permXF207 : Fin 2 → Fin 7 → Fin 7
  | 0 => pXF2070
  | 1 => pXF2071

def permXinvF207 : Fin 2 → Fin 7 → Fin 7
  | 0 => pXF2070inv
  | 1 => pXF2071inv

def eXF207 (i : Fin 2) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXF207 i) (permXinvF207 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `6`, so an invariant
operation is `6` values. -/
def repF207 : Fin 6 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (2, 0)
  | 4 => (2, 2)
  | 5 => (2, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trF207 : Fin 7 → Fin 7 → Fin 6 × Fin 20
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 2)
  | 0, 4 => (2, 4)
  | 0, 5 => (2, 6)
  | 0, 6 => (2, 8)
  | 1, 0 => (1, 10)
  | 1, 1 => (0, 10)
  | 1, 2 => (2, 10)
  | 1, 3 => (2, 12)
  | 1, 4 => (2, 14)
  | 1, 5 => (2, 16)
  | 1, 6 => (2, 18)
  | 2, 0 => (3, 0)
  | 2, 1 => (3, 10)
  | 2, 2 => (4, 0)
  | 2, 3 => (5, 0)
  | 2, 4 => (5, 1)
  | 2, 5 => (5, 10)
  | 2, 6 => (5, 11)
  | 3, 0 => (3, 2)
  | 3, 1 => (3, 12)
  | 3, 2 => (5, 2)
  | 3, 3 => (4, 2)
  | 3, 4 => (5, 12)
  | 3, 5 => (5, 3)
  | 3, 6 => (5, 13)
  | 4, 0 => (3, 4)
  | 4, 1 => (3, 14)
  | 4, 2 => (5, 4)
  | 4, 3 => (5, 14)
  | 4, 4 => (4, 4)
  | 4, 5 => (5, 15)
  | 4, 6 => (5, 5)
  | 5, 0 => (3, 6)
  | 5, 1 => (3, 16)
  | 5, 2 => (5, 16)
  | 5, 3 => (5, 6)
  | 5, 4 => (5, 17)
  | 5, 5 => (4, 6)
  | 5, 6 => (5, 7)
  | 6, 0 => (3, 8)
  | 6, 1 => (3, 18)
  | 6, 2 => (5, 18)
  | 6, 3 => (5, 19)
  | 6, 4 => (5, 8)
  | 6, 5 => (5, 9)
  | 6, 6 => (4, 8)

/-- The `10` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxF2070 : Fin 10 → Fin 20
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
def valF2070 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 1

/-- The `10` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxF2071 : Fin 10 → Fin 20
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
def valF2071 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxF2072 : Fin 2 → Fin 20
  | 0 => 0
  | 1 => 1
def valF2072 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxF2073 : Fin 2 → Fin 20
  | 0 => 0
  | 1 => 1
def valF2073 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `4` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxF2074 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 10
  | 3 => 11
def valF2074 : Fin 1 → Fin 7
  | 0 => 2

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxF2075 : Fin 1 → Fin 20
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def decF207 (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7) : Fin 6 → Fin 7
  | 0 => valF2070 a
  | 1 => valF2071 b
  | 2 => valF2072 c
  | 3 => valF2073 d
  | 4 => valF2074 e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabF207_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabF207 (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valF2070 a
  | 0, 1 => valF2071 b
  | 0, 2 => valF2072 c
  | 0, 3 => pEF2072 (valF2072 c)
  | 0, 4 => pEF2074 (valF2072 c)
  | 0, 5 => pEF2076 (valF2072 c)
  | 0, 6 => pEF2078 (valF2072 c)
  | 1, 0 => pEF20710 (valF2071 b)
  | 1, 1 => pEF20710 (valF2070 a)
  | 1, 2 => pEF20710 (valF2072 c)
  | 1, 3 => pEF20712 (valF2072 c)
  | 1, 4 => pEF20714 (valF2072 c)
  | 1, 5 => pEF20716 (valF2072 c)
  | 1, 6 => pEF20718 (valF2072 c)
  | 2, 0 => valF2073 d
  | 2, 1 => pEF20710 (valF2073 d)
  | 2, 2 => valF2074 e
  | 2, 3 => f
  | 2, 4 => pEF2071 f
  | 2, 5 => pEF20710 f
  | 2, 6 => pEF20711 f
  | 3, 0 => pEF2072 (valF2073 d)
  | 3, 1 => pEF20712 (valF2073 d)
  | 3, 2 => pEF2072 f
  | 3, 3 => pEF2072 (valF2074 e)
  | 3, 4 => pEF20712 f
  | 3, 5 => pEF2073 f
  | 3, 6 => pEF20713 f
  | 4, 0 => pEF2074 (valF2073 d)
  | 4, 1 => pEF20714 (valF2073 d)
  | 4, 2 => pEF2074 f
  | 4, 3 => pEF20714 f
  | 4, 4 => pEF2074 (valF2074 e)
  | 4, 5 => pEF20715 f
  | 4, 6 => pEF2075 f
  | 5, 0 => pEF2076 (valF2073 d)
  | 5, 1 => pEF20716 (valF2073 d)
  | 5, 2 => pEF20716 f
  | 5, 3 => pEF2076 f
  | 5, 4 => pEF20717 f
  | 5, 5 => pEF2076 (valF2074 e)
  | 5, 6 => pEF2077 f
  | 6, 0 => pEF2078 (valF2073 d)
  | 6, 1 => pEF20718 (valF2073 d)
  | 6, 2 => pEF20718 f
  | 6, 3 => pEF20719 f
  | 6, 4 => pEF2078 f
  | 6, 5 => pEF2079 f
  | 6, 6 => pEF2078 (valF2074 e)

theorem tabF207_eq_transport (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7) :
    tabF207 a b c d e f = Magma.transport permEF207 trF207 (decF207 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `72` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `252` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowF2070 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 0 0 0 0 0 0
  | 1 => tabF207 0 0 0 0 0 1
  | 2 => tabF207 0 0 0 1 0 0
  | 3 => tabF207 0 0 0 1 0 1
  | 4 => tabF207 0 0 0 2 0 0
  | 5 => tabF207 0 0 0 2 0 1
  | 6 => tabF207 0 0 1 0 0 0
  | 7 => tabF207 0 0 1 0 0 1
  | _ => tabF207 0 0 1 1 0 0
def memRowF2071 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 0 0 1 1 0 1
  | 1 => tabF207 0 0 1 2 0 0
  | 2 => tabF207 0 0 1 2 0 1
  | 3 => tabF207 0 0 2 0 0 0
  | 4 => tabF207 0 0 2 0 0 1
  | 5 => tabF207 0 0 2 1 0 0
  | 6 => tabF207 0 0 2 1 0 1
  | 7 => tabF207 0 0 2 2 0 0
  | _ => tabF207 0 0 2 2 0 1
def memRowF2072 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 0 1 0 0 0 0
  | 1 => tabF207 0 1 0 0 0 1
  | 2 => tabF207 0 1 0 1 0 0
  | 3 => tabF207 0 1 0 1 0 1
  | 4 => tabF207 0 1 0 2 0 0
  | 5 => tabF207 0 1 0 2 0 1
  | 6 => tabF207 0 1 1 0 0 0
  | 7 => tabF207 0 1 1 0 0 1
  | _ => tabF207 0 1 1 1 0 0
def memRowF2073 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 0 1 1 1 0 1
  | 1 => tabF207 0 1 1 2 0 0
  | 2 => tabF207 0 1 1 2 0 1
  | 3 => tabF207 0 1 2 0 0 0
  | 4 => tabF207 0 1 2 0 0 1
  | 5 => tabF207 0 1 2 1 0 0
  | 6 => tabF207 0 1 2 1 0 1
  | 7 => tabF207 0 1 2 2 0 0
  | _ => tabF207 0 1 2 2 0 1
def memRowF2074 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 1 0 0 0 0 0
  | 1 => tabF207 1 0 0 0 0 1
  | 2 => tabF207 1 0 0 1 0 0
  | 3 => tabF207 1 0 0 1 0 1
  | 4 => tabF207 1 0 0 2 0 0
  | 5 => tabF207 1 0 0 2 0 1
  | 6 => tabF207 1 0 1 0 0 0
  | 7 => tabF207 1 0 1 0 0 1
  | _ => tabF207 1 0 1 1 0 0
def memRowF2075 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 1 0 1 1 0 1
  | 1 => tabF207 1 0 1 2 0 0
  | 2 => tabF207 1 0 1 2 0 1
  | 3 => tabF207 1 0 2 0 0 0
  | 4 => tabF207 1 0 2 0 0 1
  | 5 => tabF207 1 0 2 1 0 0
  | 6 => tabF207 1 0 2 1 0 1
  | 7 => tabF207 1 0 2 2 0 0
  | _ => tabF207 1 0 2 2 0 1
def memRowF2076 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 1 1 0 0 0 0
  | 1 => tabF207 1 1 0 0 0 1
  | 2 => tabF207 1 1 0 1 0 0
  | 3 => tabF207 1 1 0 1 0 1
  | 4 => tabF207 1 1 0 2 0 0
  | 5 => tabF207 1 1 0 2 0 1
  | 6 => tabF207 1 1 1 0 0 0
  | 7 => tabF207 1 1 1 0 0 1
  | _ => tabF207 1 1 1 1 0 0
def memRowF2077 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF207 1 1 1 1 0 1
  | 1 => tabF207 1 1 1 2 0 0
  | 2 => tabF207 1 1 1 2 0 1
  | 3 => tabF207 1 1 2 0 0 0
  | 4 => tabF207 1 1 2 0 0 1
  | 5 => tabF207 1 1 2 1 0 0
  | 6 => tabF207 1 1 2 1 0 1
  | 7 => tabF207 1 1 2 2 0 0
  | _ => tabF207 1 1 2 2 0 1
def memF207 (i : Fin 72) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 9 : Nat) with
  | 0 => memRowF2070 ⟨i.1 % 9, by omega⟩
  | 1 => memRowF2071 ⟨i.1 % 9, by omega⟩
  | 2 => memRowF2072 ⟨i.1 % 9, by omega⟩
  | 3 => memRowF2073 ⟨i.1 % 9, by omega⟩
  | 4 => memRowF2074 ⟨i.1 % 9, by omega⟩
  | 5 => memRowF2075 ⟨i.1 % 9, by omega⟩
  | 6 => memRowF2076 ⟨i.1 % 9, by omega⟩
  | _ => memRowF2077 ⟨i.1 % 9, by omega⟩

/-- Which of the `72` members a given invariant tuple is, so that `mem_of_isExactF207` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrF207 : Array Nat := #[
  0, 1, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 6, 7, 0, 0, 0, 0, 0, 8, 9, 0, 0,
  0, 0, 0, 10, 11, 0, 0, 0, 0, 0, 12, 13, 0, 0, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 16, 17, 0, 0, 0,
  0, 0, 18, 19, 0, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0, 0, 22, 23, 0, 0, 0, 0, 0, 24, 25, 0, 0, 0, 0,
  0, 26, 27, 0, 0, 0, 0, 0, 28, 29, 0, 0, 0, 0, 0, 30, 31, 0, 0, 0, 0, 0, 32, 33, 0, 0, 0, 0, 0,
  34, 35, 0, 0, 0, 0, 0, 36, 37, 0, 0, 0, 0, 0, 38, 39, 0, 0, 0, 0, 0, 40, 41, 0, 0, 0, 0, 0, 42,
  43, 0, 0, 0, 0, 0, 44, 45, 0, 0, 0, 0, 0, 46, 47, 0, 0, 0, 0, 0, 48, 49, 0, 0, 0, 0, 0, 50, 51,
  0, 0, 0, 0, 0, 52, 53, 0, 0, 0, 0, 0, 54, 55, 0, 0, 0, 0, 0, 56, 57, 0, 0, 0, 0, 0, 58, 59, 0,
  0, 0, 0, 0, 60, 61, 0, 0, 0, 0, 0, 62, 63, 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 66, 67, 0, 0,
  0, 0, 0, 68, 69, 0, 0, 0, 0, 0, 70, 71, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArrF207` is addressed. -/
def encTF207 (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7) : Nat :=
  a.1 * 126 +
    b.1 * 63 +
    c.1 * 21 +
    d.1 * 7 +
    e.1 * 7 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankF207 (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7) : Fin 72 :=
  ⟨min (rankArrF207.getD (encTF207 a b c d e f) 0) 71, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactF207 (i : Fin 72) : Magma (Fin 7) := Magma.mk (memF207 i)

theorem exactF207_isEndo (i : Fin 72) (j : Fin 20) : (exactF207 i).IsEndo ⇑(eEF207 j) := by
  simp only [eEF207, coe_permOf]; revert i j; native_decide

theorem exactF207_not_isEndo (i : Fin 72) (j : Fin 2) : ¬ (exactF207 i).IsEndo ⇑(eXF207 j) := by
  simp only [eXF207, coe_permOf]; revert i j; native_decide

/-- `rankF207` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memF207` for the index would be a comparison per tuple and
member. -/
theorem mem_rankF207 (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7)
    (h : Magma.isExact (tabF207 a b c d e f) permEF207 permXF207 = true) :
    memF207 (rankF207 a b c d e f) = tabF207 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `72` listed
members. -/
theorem mem_of_isExactF207 (a b : Fin 2) (c d : Fin 3) (e : Fin 1) (f : Fin 7)
    (h : Magma.isExact (tabF207 a b c d e f) permEF207 permXF207 = true) :
    ∃ i, memF207 i = tabF207 a b c d e f :=
  ⟨_, mem_rankF207 a b c d e f h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactF207`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactF207` turns that into a member index. -/
theorem exists_exactF207 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eEF207 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXF207 i)) : ∃ i, exactF207 i = M := by
  simp only [eEF207, coe_permOf] at hE
  simp only [eXF207, coe_permOf] at hX
  have hop : M.op = Magma.transport permEF207 trF207 (fun i ↦ M.op (repF207 i).1 (repF207 i).2) :=
    Magma.op_eq_transport (rep := repF207) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEF207) (idx := stabIdxF2070) (a := (repF207 0).1) (b := (repF207 0).2)
    (val := valF2070) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEF207) (idx := stabIdxF2071) (a := (repF207 1).1) (b := (repF207 1).2)
    (val := valF2071) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEF207) (idx := stabIdxF2072) (a := (repF207 2).1) (b := (repF207 2).2)
    (val := valF2072) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEF207) (idx := stabIdxF2073) (a := (repF207 3).1) (b := (repF207 3).2)
    (val := valF2073) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEF207) (idx := stabIdxF2074) (a := (repF207 4).1) (b := (repF207 4).2)
    (val := valF2074) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permEF207) (idx := stabIdxF2075) (a := (repF207 5).1) (b := (repF207 5).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decF207 a b c d e f = fun i ↦ M.op (repF207 i).1 (repF207 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabF207 a b c d e f = M.op := by
    rw [tabF207_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabF207 a b c d e f) permEF207 permXF207 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactF207 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`20` group of `Magma.permEF207`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactF207 {L L' : Law.NatMagmaLaw} {i : Fin 72}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactF207 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactF207 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactF207 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactF207
    (fun k ↦ (Magma.exactF207_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactF207_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
