import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D56` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`10` group `⟨(1 2 4 5 3), (2 3)(4 5)⟩` -/

/-- The `10` elements of the group: `()`, `(2 3)(4 5)`, `(1 2)(3 4)`, `(1 2 4 5 3)`, `(1 3 5 4 2)`,
`(1 3)(2 5)`, `(1 4)(3 5)`, `(1 4 3 2 5)`, `(1 5 2 3 4)`, `(1 5)(2 4)`. -/
def pED560 : Fin 6 → Fin 6 := id
def pED561 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pED562 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5
def pED563 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 3
def pED564 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 4
def pED565 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 2
def pED566 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3
def pED567 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 2 | 4 => 3 | 5 => 1
def pED568 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 2
def pED569 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1

def permED56 : Fin 10 → Fin 6 → Fin 6
  | 0 => pED560
  | 1 => pED561
  | 2 => pED562
  | 3 => pED563
  | 4 => pED564
  | 5 => pED565
  | 6 => pED566
  | 7 => pED567
  | 8 => pED568
  | 9 => pED569

def permEinvD56 : Fin 10 → Fin 6 → Fin 6
  | 0 => pED560
  | 1 => pED561
  | 2 => pED562
  | 3 => pED564
  | 4 => pED563
  | 5 => pED565
  | 6 => pED566
  | 7 => pED568
  | 8 => pED567
  | 9 => pED569

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED56 (i : Fin 10) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permED56 i) (permEinvD56 i) (by revert i; decide)

/-- The `3` permutations that must *not* be automorphisms: `(1 2 5 3 4)`, `(1 3 4 5)`, `(0 4 5 1
2)`. Every subgroup properly containing the group above contains one of them, so a magma admitting
the group and not these has that group as its automorphism group exactly. -/
def pXD560 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 3
def pXD561 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 1
def pXD562 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 1
def pXD560inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 2
def pXD561inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 4
def pXD562inv : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 4

def permXD56 : Fin 3 → Fin 6 → Fin 6
  | 0 => pXD560
  | 1 => pXD561
  | 2 => pXD562

def permXinvD56 : Fin 3 → Fin 6 → Fin 6
  | 0 => pXD560inv
  | 1 => pXD561inv
  | 2 => pXD562inv

def eXD56 (i : Fin 3) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXD56 i) (permXinvD56 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `6`, so an invariant
operation is `6` values. -/
def repD56 : Fin 6 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)
  | 5 => (1, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD56 : Fin 6 → Fin 6 → Fin 6 × Fin 10
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 2)
  | 0, 3 => (1, 4)
  | 0, 4 => (1, 6)
  | 0, 5 => (1, 8)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (4, 1)
  | 1, 4 => (5, 0)
  | 1, 5 => (5, 1)
  | 2, 0 => (2, 2)
  | 2, 1 => (4, 2)
  | 2, 2 => (3, 2)
  | 2, 3 => (5, 2)
  | 2, 4 => (4, 3)
  | 2, 5 => (5, 3)
  | 3, 0 => (2, 4)
  | 3, 1 => (4, 4)
  | 3, 2 => (5, 4)
  | 3, 3 => (3, 4)
  | 3, 4 => (5, 5)
  | 3, 5 => (4, 5)
  | 4, 0 => (2, 6)
  | 4, 1 => (5, 6)
  | 4, 2 => (4, 6)
  | 4, 3 => (5, 7)
  | 4, 4 => (3, 6)
  | 4, 5 => (4, 7)
  | 5, 0 => (2, 8)
  | 5, 1 => (5, 8)
  | 5, 2 => (5, 9)
  | 5, 3 => (4, 8)
  | 5, 4 => (4, 9)
  | 5, 5 => (3, 8)

/-- The `10` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxD560 : Fin 10 → Fin 10
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
def valD560 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD561 : Fin 2 → Fin 10
  | 0 => 0
  | 1 => 1
def valD561 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD562 : Fin 2 → Fin 10
  | 0 => 0
  | 1 => 1
def valD562 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD563 : Fin 2 → Fin 10
  | 0 => 0
  | 1 => 1
def valD563 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxD564 : Fin 1 → Fin 10
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxD565 : Fin 1 → Fin 10
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def decD56 (a : Fin 1) (b c d : Fin 2) (e f : Fin 6) : Fin 6 → Fin 6
  | 0 => valD560 a
  | 1 => valD561 b
  | 2 => valD562 c
  | 3 => valD563 d
  | 4 => e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD56_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD56 (a : Fin 1) (b c d : Fin 2) (e f : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valD560 a
  | 0, 1 => valD561 b
  | 0, 2 => pED562 (valD561 b)
  | 0, 3 => pED564 (valD561 b)
  | 0, 4 => pED566 (valD561 b)
  | 0, 5 => pED568 (valD561 b)
  | 1, 0 => valD562 c
  | 1, 1 => valD563 d
  | 1, 2 => e
  | 1, 3 => pED561 e
  | 1, 4 => f
  | 1, 5 => pED561 f
  | 2, 0 => pED562 (valD562 c)
  | 2, 1 => pED562 e
  | 2, 2 => pED562 (valD563 d)
  | 2, 3 => pED562 f
  | 2, 4 => pED563 e
  | 2, 5 => pED563 f
  | 3, 0 => pED564 (valD562 c)
  | 3, 1 => pED564 e
  | 3, 2 => pED564 f
  | 3, 3 => pED564 (valD563 d)
  | 3, 4 => pED565 f
  | 3, 5 => pED565 e
  | 4, 0 => pED566 (valD562 c)
  | 4, 1 => pED566 f
  | 4, 2 => pED566 e
  | 4, 3 => pED567 f
  | 4, 4 => pED566 (valD563 d)
  | 4, 5 => pED567 e
  | 5, 0 => pED568 (valD562 c)
  | 5, 1 => pED568 f
  | 5, 2 => pED569 f
  | 5, 3 => pED568 e
  | 5, 4 => pED569 e
  | 5, 5 => pED568 (valD563 d)

theorem tabD56_eq_transport (a : Fin 1) (b c d : Fin 2) (e f : Fin 6) :
    tabD56 a b c d e f = Magma.transport permED56 trD56 (decD56 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `240` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `288` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowD560 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 0 0 0 1
  | 1 => tabD56 0 0 0 0 0 2
  | 2 => tabD56 0 0 0 0 0 3
  | 3 => tabD56 0 0 0 0 0 4
  | 4 => tabD56 0 0 0 0 0 5
  | 5 => tabD56 0 0 0 0 1 0
  | 6 => tabD56 0 0 0 0 1 2
  | 7 => tabD56 0 0 0 0 1 3
  | 8 => tabD56 0 0 0 0 1 4
  | 9 => tabD56 0 0 0 0 1 5
  | 10 => tabD56 0 0 0 0 2 0
  | 11 => tabD56 0 0 0 0 2 1
  | 12 => tabD56 0 0 0 0 2 2
  | 13 => tabD56 0 0 0 0 2 3
  | 14 => tabD56 0 0 0 0 2 5
  | _ => tabD56 0 0 0 0 3 0
def memRowD561 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 0 0 3 1
  | 1 => tabD56 0 0 0 0 3 2
  | 2 => tabD56 0 0 0 0 3 3
  | 3 => tabD56 0 0 0 0 3 4
  | 4 => tabD56 0 0 0 0 4 0
  | 5 => tabD56 0 0 0 0 4 1
  | 6 => tabD56 0 0 0 0 4 2
  | 7 => tabD56 0 0 0 0 4 4
  | 8 => tabD56 0 0 0 0 4 5
  | 9 => tabD56 0 0 0 0 5 0
  | 10 => tabD56 0 0 0 0 5 1
  | 11 => tabD56 0 0 0 0 5 3
  | 12 => tabD56 0 0 0 0 5 4
  | 13 => tabD56 0 0 0 0 5 5
  | 14 => tabD56 0 0 0 1 0 1
  | _ => tabD56 0 0 0 1 0 2
def memRowD562 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 0 1 0 3
  | 1 => tabD56 0 0 0 1 0 4
  | 2 => tabD56 0 0 0 1 0 5
  | 3 => tabD56 0 0 0 1 1 0
  | 4 => tabD56 0 0 0 1 1 2
  | 5 => tabD56 0 0 0 1 1 3
  | 6 => tabD56 0 0 0 1 1 4
  | 7 => tabD56 0 0 0 1 1 5
  | 8 => tabD56 0 0 0 1 2 0
  | 9 => tabD56 0 0 0 1 2 1
  | 10 => tabD56 0 0 0 1 2 2
  | 11 => tabD56 0 0 0 1 2 3
  | 12 => tabD56 0 0 0 1 2 5
  | 13 => tabD56 0 0 0 1 3 0
  | 14 => tabD56 0 0 0 1 3 1
  | _ => tabD56 0 0 0 1 3 2
def memRowD563 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 0 1 3 3
  | 1 => tabD56 0 0 0 1 3 4
  | 2 => tabD56 0 0 0 1 4 0
  | 3 => tabD56 0 0 0 1 4 1
  | 4 => tabD56 0 0 0 1 4 2
  | 5 => tabD56 0 0 0 1 4 4
  | 6 => tabD56 0 0 0 1 4 5
  | 7 => tabD56 0 0 0 1 5 0
  | 8 => tabD56 0 0 0 1 5 1
  | 9 => tabD56 0 0 0 1 5 3
  | 10 => tabD56 0 0 0 1 5 4
  | 11 => tabD56 0 0 0 1 5 5
  | 12 => tabD56 0 0 1 0 0 1
  | 13 => tabD56 0 0 1 0 0 2
  | 14 => tabD56 0 0 1 0 0 3
  | _ => tabD56 0 0 1 0 0 4
def memRowD564 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 1 0 0 5
  | 1 => tabD56 0 0 1 0 1 0
  | 2 => tabD56 0 0 1 0 1 2
  | 3 => tabD56 0 0 1 0 1 3
  | 4 => tabD56 0 0 1 0 1 4
  | 5 => tabD56 0 0 1 0 1 5
  | 6 => tabD56 0 0 1 0 2 0
  | 7 => tabD56 0 0 1 0 2 1
  | 8 => tabD56 0 0 1 0 2 2
  | 9 => tabD56 0 0 1 0 2 3
  | 10 => tabD56 0 0 1 0 2 5
  | 11 => tabD56 0 0 1 0 3 0
  | 12 => tabD56 0 0 1 0 3 1
  | 13 => tabD56 0 0 1 0 3 2
  | 14 => tabD56 0 0 1 0 3 3
  | _ => tabD56 0 0 1 0 3 4
def memRowD565 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 1 0 4 0
  | 1 => tabD56 0 0 1 0 4 1
  | 2 => tabD56 0 0 1 0 4 2
  | 3 => tabD56 0 0 1 0 4 4
  | 4 => tabD56 0 0 1 0 4 5
  | 5 => tabD56 0 0 1 0 5 0
  | 6 => tabD56 0 0 1 0 5 1
  | 7 => tabD56 0 0 1 0 5 3
  | 8 => tabD56 0 0 1 0 5 4
  | 9 => tabD56 0 0 1 0 5 5
  | 10 => tabD56 0 0 1 1 0 1
  | 11 => tabD56 0 0 1 1 0 2
  | 12 => tabD56 0 0 1 1 0 3
  | 13 => tabD56 0 0 1 1 0 4
  | 14 => tabD56 0 0 1 1 0 5
  | _ => tabD56 0 0 1 1 1 0
def memRowD566 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 1 1 1 2
  | 1 => tabD56 0 0 1 1 1 3
  | 2 => tabD56 0 0 1 1 1 4
  | 3 => tabD56 0 0 1 1 1 5
  | 4 => tabD56 0 0 1 1 2 0
  | 5 => tabD56 0 0 1 1 2 1
  | 6 => tabD56 0 0 1 1 2 2
  | 7 => tabD56 0 0 1 1 2 3
  | 8 => tabD56 0 0 1 1 2 5
  | 9 => tabD56 0 0 1 1 3 0
  | 10 => tabD56 0 0 1 1 3 1
  | 11 => tabD56 0 0 1 1 3 2
  | 12 => tabD56 0 0 1 1 3 3
  | 13 => tabD56 0 0 1 1 3 4
  | 14 => tabD56 0 0 1 1 4 0
  | _ => tabD56 0 0 1 1 4 1
def memRowD567 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 0 1 1 4 2
  | 1 => tabD56 0 0 1 1 4 4
  | 2 => tabD56 0 0 1 1 4 5
  | 3 => tabD56 0 0 1 1 5 0
  | 4 => tabD56 0 0 1 1 5 1
  | 5 => tabD56 0 0 1 1 5 3
  | 6 => tabD56 0 0 1 1 5 4
  | 7 => tabD56 0 0 1 1 5 5
  | 8 => tabD56 0 1 0 0 0 1
  | 9 => tabD56 0 1 0 0 0 2
  | 10 => tabD56 0 1 0 0 0 3
  | 11 => tabD56 0 1 0 0 0 4
  | 12 => tabD56 0 1 0 0 0 5
  | 13 => tabD56 0 1 0 0 1 0
  | 14 => tabD56 0 1 0 0 1 2
  | _ => tabD56 0 1 0 0 1 3
def memRowD568 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 0 0 1 4
  | 1 => tabD56 0 1 0 0 1 5
  | 2 => tabD56 0 1 0 0 2 0
  | 3 => tabD56 0 1 0 0 2 1
  | 4 => tabD56 0 1 0 0 2 2
  | 5 => tabD56 0 1 0 0 2 3
  | 6 => tabD56 0 1 0 0 2 5
  | 7 => tabD56 0 1 0 0 3 0
  | 8 => tabD56 0 1 0 0 3 1
  | 9 => tabD56 0 1 0 0 3 2
  | 10 => tabD56 0 1 0 0 3 3
  | 11 => tabD56 0 1 0 0 3 4
  | 12 => tabD56 0 1 0 0 4 0
  | 13 => tabD56 0 1 0 0 4 1
  | 14 => tabD56 0 1 0 0 4 2
  | _ => tabD56 0 1 0 0 4 4
def memRowD569 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 0 0 4 5
  | 1 => tabD56 0 1 0 0 5 0
  | 2 => tabD56 0 1 0 0 5 1
  | 3 => tabD56 0 1 0 0 5 3
  | 4 => tabD56 0 1 0 0 5 4
  | 5 => tabD56 0 1 0 0 5 5
  | 6 => tabD56 0 1 0 1 0 1
  | 7 => tabD56 0 1 0 1 0 2
  | 8 => tabD56 0 1 0 1 0 3
  | 9 => tabD56 0 1 0 1 0 4
  | 10 => tabD56 0 1 0 1 0 5
  | 11 => tabD56 0 1 0 1 1 0
  | 12 => tabD56 0 1 0 1 1 2
  | 13 => tabD56 0 1 0 1 1 3
  | 14 => tabD56 0 1 0 1 1 4
  | _ => tabD56 0 1 0 1 1 5
def memRowD5610 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 0 1 2 0
  | 1 => tabD56 0 1 0 1 2 1
  | 2 => tabD56 0 1 0 1 2 2
  | 3 => tabD56 0 1 0 1 2 3
  | 4 => tabD56 0 1 0 1 2 5
  | 5 => tabD56 0 1 0 1 3 0
  | 6 => tabD56 0 1 0 1 3 1
  | 7 => tabD56 0 1 0 1 3 2
  | 8 => tabD56 0 1 0 1 3 3
  | 9 => tabD56 0 1 0 1 3 4
  | 10 => tabD56 0 1 0 1 4 0
  | 11 => tabD56 0 1 0 1 4 1
  | 12 => tabD56 0 1 0 1 4 2
  | 13 => tabD56 0 1 0 1 4 4
  | 14 => tabD56 0 1 0 1 4 5
  | _ => tabD56 0 1 0 1 5 0
def memRowD5611 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 0 1 5 1
  | 1 => tabD56 0 1 0 1 5 3
  | 2 => tabD56 0 1 0 1 5 4
  | 3 => tabD56 0 1 0 1 5 5
  | 4 => tabD56 0 1 1 0 0 1
  | 5 => tabD56 0 1 1 0 0 2
  | 6 => tabD56 0 1 1 0 0 3
  | 7 => tabD56 0 1 1 0 0 4
  | 8 => tabD56 0 1 1 0 0 5
  | 9 => tabD56 0 1 1 0 1 0
  | 10 => tabD56 0 1 1 0 1 2
  | 11 => tabD56 0 1 1 0 1 3
  | 12 => tabD56 0 1 1 0 1 4
  | 13 => tabD56 0 1 1 0 1 5
  | 14 => tabD56 0 1 1 0 2 0
  | _ => tabD56 0 1 1 0 2 1
def memRowD5612 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 1 0 2 2
  | 1 => tabD56 0 1 1 0 2 3
  | 2 => tabD56 0 1 1 0 2 5
  | 3 => tabD56 0 1 1 0 3 0
  | 4 => tabD56 0 1 1 0 3 1
  | 5 => tabD56 0 1 1 0 3 2
  | 6 => tabD56 0 1 1 0 3 3
  | 7 => tabD56 0 1 1 0 3 4
  | 8 => tabD56 0 1 1 0 4 0
  | 9 => tabD56 0 1 1 0 4 1
  | 10 => tabD56 0 1 1 0 4 2
  | 11 => tabD56 0 1 1 0 4 4
  | 12 => tabD56 0 1 1 0 4 5
  | 13 => tabD56 0 1 1 0 5 0
  | 14 => tabD56 0 1 1 0 5 1
  | _ => tabD56 0 1 1 0 5 3
def memRowD5613 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 1 0 5 4
  | 1 => tabD56 0 1 1 0 5 5
  | 2 => tabD56 0 1 1 1 0 1
  | 3 => tabD56 0 1 1 1 0 2
  | 4 => tabD56 0 1 1 1 0 3
  | 5 => tabD56 0 1 1 1 0 4
  | 6 => tabD56 0 1 1 1 0 5
  | 7 => tabD56 0 1 1 1 1 0
  | 8 => tabD56 0 1 1 1 1 2
  | 9 => tabD56 0 1 1 1 1 3
  | 10 => tabD56 0 1 1 1 1 4
  | 11 => tabD56 0 1 1 1 1 5
  | 12 => tabD56 0 1 1 1 2 0
  | 13 => tabD56 0 1 1 1 2 1
  | 14 => tabD56 0 1 1 1 2 2
  | _ => tabD56 0 1 1 1 2 3
def memRowD5614 : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD56 0 1 1 1 2 5
  | 1 => tabD56 0 1 1 1 3 0
  | 2 => tabD56 0 1 1 1 3 1
  | 3 => tabD56 0 1 1 1 3 2
  | 4 => tabD56 0 1 1 1 3 3
  | 5 => tabD56 0 1 1 1 3 4
  | 6 => tabD56 0 1 1 1 4 0
  | 7 => tabD56 0 1 1 1 4 1
  | 8 => tabD56 0 1 1 1 4 2
  | 9 => tabD56 0 1 1 1 4 4
  | 10 => tabD56 0 1 1 1 4 5
  | 11 => tabD56 0 1 1 1 5 0
  | 12 => tabD56 0 1 1 1 5 1
  | 13 => tabD56 0 1 1 1 5 3
  | 14 => tabD56 0 1 1 1 5 4
  | _ => tabD56 0 1 1 1 5 5
def memD56 (i : Fin 240) : Fin 6 → Fin 6 → Fin 6 :=
  match (i.1 / 16 : Nat) with
  | 0 => memRowD560 ⟨i.1 % 16, by omega⟩
  | 1 => memRowD561 ⟨i.1 % 16, by omega⟩
  | 2 => memRowD562 ⟨i.1 % 16, by omega⟩
  | 3 => memRowD563 ⟨i.1 % 16, by omega⟩
  | 4 => memRowD564 ⟨i.1 % 16, by omega⟩
  | 5 => memRowD565 ⟨i.1 % 16, by omega⟩
  | 6 => memRowD566 ⟨i.1 % 16, by omega⟩
  | 7 => memRowD567 ⟨i.1 % 16, by omega⟩
  | 8 => memRowD568 ⟨i.1 % 16, by omega⟩
  | 9 => memRowD569 ⟨i.1 % 16, by omega⟩
  | 10 => memRowD5610 ⟨i.1 % 16, by omega⟩
  | 11 => memRowD5611 ⟨i.1 % 16, by omega⟩
  | 12 => memRowD5612 ⟨i.1 % 16, by omega⟩
  | 13 => memRowD5613 ⟨i.1 % 16, by omega⟩
  | _ => memRowD5614 ⟨i.1 % 16, by omega⟩

/-- Which of the `240` members a given invariant tuple is, so that `mem_of_isExactD56` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD56 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12, 13, 0, 14, 15, 16, 17, 18, 19, 0, 20, 21, 22,
  0, 23, 24, 25, 26, 0, 27, 28, 29, 0, 30, 31, 32, 33, 34, 35, 0, 36, 37, 38, 39, 40, 41, 42, 43,
  0, 44, 45, 46, 47, 48, 49, 0, 50, 51, 52, 0, 53, 54, 55, 56, 0, 57, 58, 59, 0, 60, 61, 62, 63,
  64, 65, 0, 66, 67, 68, 69, 70, 71, 72, 73, 0, 74, 75, 76, 77, 78, 79, 0, 80, 81, 82, 0, 83, 84,
  85, 86, 0, 87, 88, 89, 0, 90, 91, 92, 93, 94, 95, 0, 96, 97, 98, 99, 100, 101, 102, 103, 0,
  104, 105, 106, 107, 108, 109, 0, 110, 111, 112, 0, 113, 114, 115, 116, 0, 117, 118, 119, 0,
  120, 121, 122, 123, 124, 125, 0, 126, 127, 128, 129, 130, 131, 132, 133, 0, 134, 135, 136, 137,
  138, 139, 0, 140, 141, 142, 0, 143, 144, 145, 146, 0, 147, 148, 149, 0, 150, 151, 152, 153,
  154, 155, 0, 156, 157, 158, 159, 160, 161, 162, 163, 0, 164, 165, 166, 167, 168, 169, 0, 170,
  171, 172, 0, 173, 174, 175, 176, 0, 177, 178, 179, 0, 180, 181, 182, 183, 184, 185, 0, 186,
  187, 188, 189, 190, 191, 192, 193, 0, 194, 195, 196, 197, 198, 199, 0, 200, 201, 202, 0, 203,
  204, 205, 206, 0, 207, 208, 209, 0, 210, 211, 212, 213, 214, 215, 0, 216, 217, 218, 219, 220,
  221, 222, 223, 0, 224, 225, 226, 227, 228, 229, 0, 230, 231, 232, 0, 233, 234, 235, 236, 0,
  237, 238, 239]

/-- The arguments as one mixed-radix index, which is how `rankArrD56` is addressed. -/
def encTD56 (a : Fin 1) (b c d : Fin 2) (e f : Fin 6) : Nat :=
  a.1 * 288 +
    b.1 * 144 +
    c.1 * 72 +
    d.1 * 36 +
    e.1 * 6 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD56 (a : Fin 1) (b c d : Fin 2) (e f : Fin 6) : Fin 240 :=
  ⟨min (rankArrD56.getD (encTD56 a b c d e f) 0) 239, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD56 (i : Fin 240) : Magma (Fin 6) := Magma.mk (memD56 i)

theorem exactD56_isEndo (i : Fin 240) (j : Fin 10) : (exactD56 i).IsEndo ⇑(eED56 j) := by
  simp only [eED56, coe_permOf]; revert i j; native_decide

theorem exactD56_not_isEndo (i : Fin 240) (j : Fin 3) : ¬ (exactD56 i).IsEndo ⇑(eXD56 j) := by
  simp only [eXD56, coe_permOf]; revert i j; native_decide

/-- `rankD56` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD56` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD56 (a : Fin 1) (b c d : Fin 2) (e f : Fin 6)
    (h : Magma.isExact (tabD56 a b c d e f) permED56 permXD56 = true) :
    memD56 (rankD56 a b c d e f) = tabD56 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `240`
listed members. -/
theorem mem_of_isExactD56 (a : Fin 1) (b c d : Fin 2) (e f : Fin 6)
    (h : Magma.isExact (tabD56 a b c d e f) permED56 permXD56 = true) :
    ∃ i, memD56 i = tabD56 a b c d e f :=
  ⟨_, mem_rankD56 a b c d e f h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD56`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD56` turns that into a member index. -/
theorem exists_exactD56 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eED56 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD56 i)) : ∃ i, exactD56 i = M := by
  simp only [eED56, coe_permOf] at hE
  simp only [eXD56, coe_permOf] at hX
  have hop : M.op = Magma.transport permED56 trD56 (fun i ↦ M.op (repD56 i).1 (repD56 i).2) :=
    Magma.op_eq_transport (rep := repD56) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED56) (idx := stabIdxD560) (a := (repD56 0).1) (b := (repD56 0).2)
    (val := valD560) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED56) (idx := stabIdxD561) (a := (repD56 1).1) (b := (repD56 1).2)
    (val := valD561) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED56) (idx := stabIdxD562) (a := (repD56 2).1) (b := (repD56 2).2)
    (val := valD562) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permED56) (idx := stabIdxD563) (a := (repD56 3).1) (b := (repD56 3).2)
    (val := valD563) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permED56) (idx := stabIdxD564) (a := (repD56 4).1) (b := (repD56 4).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permED56) (idx := stabIdxD565) (a := (repD56 5).1) (b := (repD56 5).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decD56 a b c d e f = fun i ↦ M.op (repD56 i).1 (repD56 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabD56 a b c d e f = M.op := by
    rw [tabD56_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD56 a b c d e f) permED56 permXD56 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD56 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`10` group of `Magma.permED56`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD56 {L L' : Law.NatMagmaLaw} {i : Fin 240}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactD56 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactD56 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD56 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD56
    (fun k ↦ (Magma.exactD56_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD56_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
