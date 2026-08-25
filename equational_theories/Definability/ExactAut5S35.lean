import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S35` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`6` group `⟨(1 2)(3 4), (0 1)(3 4)⟩` -/

/-- The `6` elements of the group: `()`, `(1 2)(3 4)`, `(0 1)(3 4)`, `(0 1 2)`, `(0 2 1)`, `(0 2)(3
4)`. -/
def pES350 : Fin 5 → Fin 5 := id
def pES351 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3
def pES352 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3
def pES353 : Fin 5 → Fin 5 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4
def pES354 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4
def pES355 : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3

def permES35 : Fin 6 → Fin 5 → Fin 5
  | 0 => pES350
  | 1 => pES351
  | 2 => pES352
  | 3 => pES353
  | 4 => pES354
  | 5 => pES355

def permEinvS35 : Fin 6 → Fin 5 → Fin 5
  | 0 => pES350
  | 1 => pES351
  | 2 => pES352
  | 3 => pES354
  | 4 => pES353
  | 5 => pES355

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES35 (i : Fin 6) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permES35 i) (permEinvS35 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(0 2 1)(3 4)`, `(0 2 4 3 1)`. Every
subgroup properly containing the group above contains one of them, so a magma admitting the group
and not these has that group as its automorphism group exactly. -/
def pXS350 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3
def pXS351 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 3
def pXS350inv : Fin 5 → Fin 5 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3
def pXS351inv : Fin 5 → Fin 5 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 2

def permXS35 : Fin 2 → Fin 5 → Fin 5
  | 0 => pXS350
  | 1 => pXS351

def permXinvS35 : Fin 2 → Fin 5 → Fin 5
  | 0 => pXS350inv
  | 1 => pXS351inv

def eXS35 (i : Fin 2) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXS35 i) (permXinvS35 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `6`, so an invariant
operation is `6` values. -/
def repS35 : Fin 6 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (3, 0)
  | 4 => (3, 3)
  | 5 => (3, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS35 : Fin 5 → Fin 5 → Fin 6 × Fin 6
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (2, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 3)
  | 1, 3 => (2, 3)
  | 1, 4 => (2, 2)
  | 2, 0 => (1, 4)
  | 2, 1 => (1, 5)
  | 2, 2 => (0, 4)
  | 2, 3 => (2, 4)
  | 2, 4 => (2, 5)
  | 3, 0 => (3, 0)
  | 3, 1 => (3, 3)
  | 3, 2 => (3, 4)
  | 3, 3 => (4, 0)
  | 3, 4 => (5, 0)
  | 4, 0 => (3, 1)
  | 4, 1 => (3, 2)
  | 4, 2 => (3, 5)
  | 4, 3 => (5, 1)
  | 4, 4 => (4, 1)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS350 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def valS350 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxS351 : Fin 1 → Fin 6
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxS352 : Fin 1 → Fin 6
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxS353 : Fin 1 → Fin 6
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `3`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS354 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def valS354 : Fin 2 → Fin 5
  | 0 => 3
  | 1 => 4

/-- The `3` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `3`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS355 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def valS355 : Fin 2 → Fin 5
  | 0 => 3
  | 1 => 4

/-- The `6` orbit values named by the family's arguments. -/
def decS35 (a : Fin 1) (b c d : Fin 5) (e f : Fin 2) : Fin 6 → Fin 5
  | 0 => valS350 a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => valS354 e
  | 5 => valS355 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS35_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS35 (a : Fin 1) (b c d : Fin 5) (e f : Fin 2) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valS350 a
  | 0, 1 => b
  | 0, 2 => pES351 b
  | 0, 3 => c
  | 0, 4 => pES351 c
  | 1, 0 => pES352 b
  | 1, 1 => pES352 (valS350 a)
  | 1, 2 => pES353 b
  | 1, 3 => pES353 c
  | 1, 4 => pES352 c
  | 2, 0 => pES354 b
  | 2, 1 => pES355 b
  | 2, 2 => pES354 (valS350 a)
  | 2, 3 => pES354 c
  | 2, 4 => pES355 c
  | 3, 0 => d
  | 3, 1 => pES353 d
  | 3, 2 => pES354 d
  | 3, 3 => valS354 e
  | 3, 4 => valS355 f
  | 4, 0 => pES351 d
  | 4, 1 => pES352 d
  | 4, 2 => pES355 d
  | 4, 3 => pES351 (valS355 f)
  | 4, 4 => pES351 (valS354 e)

theorem tabS35_eq_transport (a : Fin 1) (b c d : Fin 5) (e f : Fin 2) :
    tabS35 a b c d e f = Magma.transport permES35 trS35 (decS35 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `392` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `500` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowS350 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 0 0 1 0 0
  | 1 => tabS35 0 0 0 1 0 1
  | 2 => tabS35 0 0 0 1 1 0
  | 3 => tabS35 0 0 0 1 1 1
  | 4 => tabS35 0 0 0 2 0 0
  | 5 => tabS35 0 0 0 2 0 1
  | 6 => tabS35 0 0 0 2 1 0
  | 7 => tabS35 0 0 0 2 1 1
  | 8 => tabS35 0 0 1 0 0 0
  | 9 => tabS35 0 0 1 0 0 1
  | 10 => tabS35 0 0 1 0 1 0
  | 11 => tabS35 0 0 1 0 1 1
  | 12 => tabS35 0 0 1 1 0 0
  | 13 => tabS35 0 0 1 1 0 1
  | 14 => tabS35 0 0 1 1 1 0
  | 15 => tabS35 0 0 1 1 1 1
  | 16 => tabS35 0 0 1 2 0 0
  | 17 => tabS35 0 0 1 2 0 1
  | 18 => tabS35 0 0 1 2 1 0
  | _ => tabS35 0 0 1 2 1 1
def memRowS351 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 0 1 3 0 0
  | 1 => tabS35 0 0 1 3 0 1
  | 2 => tabS35 0 0 1 3 1 0
  | 3 => tabS35 0 0 1 3 1 1
  | 4 => tabS35 0 0 1 4 0 0
  | 5 => tabS35 0 0 1 4 0 1
  | 6 => tabS35 0 0 1 4 1 0
  | 7 => tabS35 0 0 1 4 1 1
  | 8 => tabS35 0 0 2 0 0 0
  | 9 => tabS35 0 0 2 0 0 1
  | 10 => tabS35 0 0 2 0 1 0
  | 11 => tabS35 0 0 2 0 1 1
  | 12 => tabS35 0 0 2 1 0 0
  | 13 => tabS35 0 0 2 1 0 1
  | 14 => tabS35 0 0 2 1 1 0
  | 15 => tabS35 0 0 2 1 1 1
  | 16 => tabS35 0 0 2 2 0 0
  | 17 => tabS35 0 0 2 2 0 1
  | 18 => tabS35 0 0 2 2 1 0
  | _ => tabS35 0 0 2 2 1 1
def memRowS352 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 0 2 3 0 0
  | 1 => tabS35 0 0 2 3 0 1
  | 2 => tabS35 0 0 2 3 1 0
  | 3 => tabS35 0 0 2 3 1 1
  | 4 => tabS35 0 0 2 4 0 0
  | 5 => tabS35 0 0 2 4 0 1
  | 6 => tabS35 0 0 2 4 1 0
  | 7 => tabS35 0 0 2 4 1 1
  | 8 => tabS35 0 0 3 1 0 0
  | 9 => tabS35 0 0 3 1 0 1
  | 10 => tabS35 0 0 3 1 1 0
  | 11 => tabS35 0 0 3 1 1 1
  | 12 => tabS35 0 0 3 2 0 0
  | 13 => tabS35 0 0 3 2 0 1
  | 14 => tabS35 0 0 3 2 1 0
  | 15 => tabS35 0 0 3 2 1 1
  | 16 => tabS35 0 0 4 1 0 0
  | 17 => tabS35 0 0 4 1 0 1
  | 18 => tabS35 0 0 4 1 1 0
  | _ => tabS35 0 0 4 1 1 1
def memRowS353 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 0 4 2 0 0
  | 1 => tabS35 0 0 4 2 0 1
  | 2 => tabS35 0 0 4 2 1 0
  | 3 => tabS35 0 0 4 2 1 1
  | 4 => tabS35 0 1 0 1 0 0
  | 5 => tabS35 0 1 0 1 0 1
  | 6 => tabS35 0 1 0 1 1 0
  | 7 => tabS35 0 1 0 1 1 1
  | 8 => tabS35 0 1 0 2 0 0
  | 9 => tabS35 0 1 0 2 0 1
  | 10 => tabS35 0 1 0 2 1 0
  | 11 => tabS35 0 1 0 2 1 1
  | 12 => tabS35 0 1 1 0 0 0
  | 13 => tabS35 0 1 1 0 0 1
  | 14 => tabS35 0 1 1 0 1 0
  | 15 => tabS35 0 1 1 0 1 1
  | 16 => tabS35 0 1 1 1 0 0
  | 17 => tabS35 0 1 1 1 0 1
  | 18 => tabS35 0 1 1 1 1 0
  | _ => tabS35 0 1 1 1 1 1
def memRowS354 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 1 1 2 0 0
  | 1 => tabS35 0 1 1 2 0 1
  | 2 => tabS35 0 1 1 2 1 0
  | 3 => tabS35 0 1 1 2 1 1
  | 4 => tabS35 0 1 1 3 0 0
  | 5 => tabS35 0 1 1 3 0 1
  | 6 => tabS35 0 1 1 3 1 0
  | 7 => tabS35 0 1 1 3 1 1
  | 8 => tabS35 0 1 1 4 0 0
  | 9 => tabS35 0 1 1 4 0 1
  | 10 => tabS35 0 1 1 4 1 0
  | 11 => tabS35 0 1 1 4 1 1
  | 12 => tabS35 0 1 2 0 0 0
  | 13 => tabS35 0 1 2 0 0 1
  | 14 => tabS35 0 1 2 0 1 0
  | 15 => tabS35 0 1 2 0 1 1
  | 16 => tabS35 0 1 2 1 0 0
  | 17 => tabS35 0 1 2 1 0 1
  | 18 => tabS35 0 1 2 1 1 0
  | _ => tabS35 0 1 2 1 1 1
def memRowS355 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 1 2 2 0 0
  | 1 => tabS35 0 1 2 2 0 1
  | 2 => tabS35 0 1 2 2 1 0
  | 3 => tabS35 0 1 2 2 1 1
  | 4 => tabS35 0 1 2 3 0 0
  | 5 => tabS35 0 1 2 3 0 1
  | 6 => tabS35 0 1 2 3 1 0
  | 7 => tabS35 0 1 2 3 1 1
  | 8 => tabS35 0 1 2 4 0 0
  | 9 => tabS35 0 1 2 4 0 1
  | 10 => tabS35 0 1 2 4 1 0
  | 11 => tabS35 0 1 2 4 1 1
  | 12 => tabS35 0 1 3 1 0 0
  | 13 => tabS35 0 1 3 1 0 1
  | 14 => tabS35 0 1 3 1 1 0
  | 15 => tabS35 0 1 3 1 1 1
  | 16 => tabS35 0 1 3 2 0 0
  | 17 => tabS35 0 1 3 2 0 1
  | 18 => tabS35 0 1 3 2 1 0
  | _ => tabS35 0 1 3 2 1 1
def memRowS356 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 1 4 1 0 0
  | 1 => tabS35 0 1 4 1 0 1
  | 2 => tabS35 0 1 4 1 1 0
  | 3 => tabS35 0 1 4 1 1 1
  | 4 => tabS35 0 1 4 2 0 0
  | 5 => tabS35 0 1 4 2 0 1
  | 6 => tabS35 0 1 4 2 1 0
  | 7 => tabS35 0 1 4 2 1 1
  | 8 => tabS35 0 2 0 1 0 0
  | 9 => tabS35 0 2 0 1 0 1
  | 10 => tabS35 0 2 0 1 1 0
  | 11 => tabS35 0 2 0 1 1 1
  | 12 => tabS35 0 2 0 2 0 0
  | 13 => tabS35 0 2 0 2 0 1
  | 14 => tabS35 0 2 0 2 1 0
  | 15 => tabS35 0 2 0 2 1 1
  | 16 => tabS35 0 2 1 0 0 0
  | 17 => tabS35 0 2 1 0 0 1
  | 18 => tabS35 0 2 1 0 1 0
  | _ => tabS35 0 2 1 0 1 1
def memRowS357 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 2 1 1 0 0
  | 1 => tabS35 0 2 1 1 0 1
  | 2 => tabS35 0 2 1 1 1 0
  | 3 => tabS35 0 2 1 1 1 1
  | 4 => tabS35 0 2 1 2 0 0
  | 5 => tabS35 0 2 1 2 0 1
  | 6 => tabS35 0 2 1 2 1 0
  | 7 => tabS35 0 2 1 2 1 1
  | 8 => tabS35 0 2 1 3 0 0
  | 9 => tabS35 0 2 1 3 0 1
  | 10 => tabS35 0 2 1 3 1 0
  | 11 => tabS35 0 2 1 3 1 1
  | 12 => tabS35 0 2 1 4 0 0
  | 13 => tabS35 0 2 1 4 0 1
  | 14 => tabS35 0 2 1 4 1 0
  | 15 => tabS35 0 2 1 4 1 1
  | 16 => tabS35 0 2 2 0 0 0
  | 17 => tabS35 0 2 2 0 0 1
  | 18 => tabS35 0 2 2 0 1 0
  | _ => tabS35 0 2 2 0 1 1
def memRowS358 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 2 2 1 0 0
  | 1 => tabS35 0 2 2 1 0 1
  | 2 => tabS35 0 2 2 1 1 0
  | 3 => tabS35 0 2 2 1 1 1
  | 4 => tabS35 0 2 2 2 0 0
  | 5 => tabS35 0 2 2 2 0 1
  | 6 => tabS35 0 2 2 2 1 0
  | 7 => tabS35 0 2 2 2 1 1
  | 8 => tabS35 0 2 2 3 0 0
  | 9 => tabS35 0 2 2 3 0 1
  | 10 => tabS35 0 2 2 3 1 0
  | 11 => tabS35 0 2 2 3 1 1
  | 12 => tabS35 0 2 2 4 0 0
  | 13 => tabS35 0 2 2 4 0 1
  | 14 => tabS35 0 2 2 4 1 0
  | 15 => tabS35 0 2 2 4 1 1
  | 16 => tabS35 0 2 3 1 0 0
  | 17 => tabS35 0 2 3 1 0 1
  | 18 => tabS35 0 2 3 1 1 0
  | _ => tabS35 0 2 3 1 1 1
def memRowS359 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 2 3 2 0 0
  | 1 => tabS35 0 2 3 2 0 1
  | 2 => tabS35 0 2 3 2 1 0
  | 3 => tabS35 0 2 3 2 1 1
  | 4 => tabS35 0 2 4 1 0 0
  | 5 => tabS35 0 2 4 1 0 1
  | 6 => tabS35 0 2 4 1 1 0
  | 7 => tabS35 0 2 4 1 1 1
  | 8 => tabS35 0 2 4 2 0 0
  | 9 => tabS35 0 2 4 2 0 1
  | 10 => tabS35 0 2 4 2 1 0
  | 11 => tabS35 0 2 4 2 1 1
  | 12 => tabS35 0 3 0 0 0 0
  | 13 => tabS35 0 3 0 0 0 1
  | 14 => tabS35 0 3 0 0 1 0
  | 15 => tabS35 0 3 0 0 1 1
  | 16 => tabS35 0 3 0 1 0 0
  | 17 => tabS35 0 3 0 1 0 1
  | 18 => tabS35 0 3 0 1 1 0
  | _ => tabS35 0 3 0 1 1 1
def memRowS3510 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 3 0 2 0 0
  | 1 => tabS35 0 3 0 2 0 1
  | 2 => tabS35 0 3 0 2 1 0
  | 3 => tabS35 0 3 0 2 1 1
  | 4 => tabS35 0 3 0 3 0 0
  | 5 => tabS35 0 3 0 3 0 1
  | 6 => tabS35 0 3 0 3 1 0
  | 7 => tabS35 0 3 0 3 1 1
  | 8 => tabS35 0 3 0 4 0 0
  | 9 => tabS35 0 3 0 4 0 1
  | 10 => tabS35 0 3 0 4 1 0
  | 11 => tabS35 0 3 0 4 1 1
  | 12 => tabS35 0 3 1 0 0 0
  | 13 => tabS35 0 3 1 0 0 1
  | 14 => tabS35 0 3 1 0 1 0
  | 15 => tabS35 0 3 1 0 1 1
  | 16 => tabS35 0 3 1 1 0 0
  | 17 => tabS35 0 3 1 1 0 1
  | 18 => tabS35 0 3 1 1 1 0
  | _ => tabS35 0 3 1 1 1 1
def memRowS3511 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 3 1 2 0 0
  | 1 => tabS35 0 3 1 2 0 1
  | 2 => tabS35 0 3 1 2 1 0
  | 3 => tabS35 0 3 1 2 1 1
  | 4 => tabS35 0 3 1 3 0 0
  | 5 => tabS35 0 3 1 3 0 1
  | 6 => tabS35 0 3 1 3 1 0
  | 7 => tabS35 0 3 1 3 1 1
  | 8 => tabS35 0 3 1 4 0 0
  | 9 => tabS35 0 3 1 4 0 1
  | 10 => tabS35 0 3 1 4 1 0
  | 11 => tabS35 0 3 1 4 1 1
  | 12 => tabS35 0 3 2 0 0 0
  | 13 => tabS35 0 3 2 0 0 1
  | 14 => tabS35 0 3 2 0 1 0
  | 15 => tabS35 0 3 2 0 1 1
  | 16 => tabS35 0 3 2 1 0 0
  | 17 => tabS35 0 3 2 1 0 1
  | 18 => tabS35 0 3 2 1 1 0
  | _ => tabS35 0 3 2 1 1 1
def memRowS3512 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 3 2 2 0 0
  | 1 => tabS35 0 3 2 2 0 1
  | 2 => tabS35 0 3 2 2 1 0
  | 3 => tabS35 0 3 2 2 1 1
  | 4 => tabS35 0 3 2 3 0 0
  | 5 => tabS35 0 3 2 3 0 1
  | 6 => tabS35 0 3 2 3 1 0
  | 7 => tabS35 0 3 2 3 1 1
  | 8 => tabS35 0 3 2 4 0 0
  | 9 => tabS35 0 3 2 4 0 1
  | 10 => tabS35 0 3 2 4 1 0
  | 11 => tabS35 0 3 2 4 1 1
  | 12 => tabS35 0 3 3 0 0 0
  | 13 => tabS35 0 3 3 0 0 1
  | 14 => tabS35 0 3 3 0 1 0
  | 15 => tabS35 0 3 3 0 1 1
  | 16 => tabS35 0 3 3 1 0 0
  | 17 => tabS35 0 3 3 1 0 1
  | 18 => tabS35 0 3 3 1 1 0
  | _ => tabS35 0 3 3 1 1 1
def memRowS3513 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 3 3 2 0 0
  | 1 => tabS35 0 3 3 2 0 1
  | 2 => tabS35 0 3 3 2 1 0
  | 3 => tabS35 0 3 3 2 1 1
  | 4 => tabS35 0 3 3 3 0 0
  | 5 => tabS35 0 3 3 3 0 1
  | 6 => tabS35 0 3 3 3 1 0
  | 7 => tabS35 0 3 3 3 1 1
  | 8 => tabS35 0 3 3 4 0 0
  | 9 => tabS35 0 3 3 4 0 1
  | 10 => tabS35 0 3 3 4 1 0
  | 11 => tabS35 0 3 3 4 1 1
  | 12 => tabS35 0 3 4 0 0 0
  | 13 => tabS35 0 3 4 0 0 1
  | 14 => tabS35 0 3 4 0 1 0
  | 15 => tabS35 0 3 4 0 1 1
  | 16 => tabS35 0 3 4 1 0 0
  | 17 => tabS35 0 3 4 1 0 1
  | 18 => tabS35 0 3 4 1 1 0
  | _ => tabS35 0 3 4 1 1 1
def memRowS3514 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 3 4 2 0 0
  | 1 => tabS35 0 3 4 2 0 1
  | 2 => tabS35 0 3 4 2 1 0
  | 3 => tabS35 0 3 4 2 1 1
  | 4 => tabS35 0 3 4 3 0 0
  | 5 => tabS35 0 3 4 3 0 1
  | 6 => tabS35 0 3 4 3 1 0
  | 7 => tabS35 0 3 4 3 1 1
  | 8 => tabS35 0 3 4 4 0 0
  | 9 => tabS35 0 3 4 4 0 1
  | 10 => tabS35 0 3 4 4 1 0
  | 11 => tabS35 0 3 4 4 1 1
  | 12 => tabS35 0 4 0 0 0 0
  | 13 => tabS35 0 4 0 0 0 1
  | 14 => tabS35 0 4 0 0 1 0
  | 15 => tabS35 0 4 0 0 1 1
  | 16 => tabS35 0 4 0 1 0 0
  | 17 => tabS35 0 4 0 1 0 1
  | 18 => tabS35 0 4 0 1 1 0
  | _ => tabS35 0 4 0 1 1 1
def memRowS3515 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 4 0 2 0 0
  | 1 => tabS35 0 4 0 2 0 1
  | 2 => tabS35 0 4 0 2 1 0
  | 3 => tabS35 0 4 0 2 1 1
  | 4 => tabS35 0 4 0 3 0 0
  | 5 => tabS35 0 4 0 3 0 1
  | 6 => tabS35 0 4 0 3 1 0
  | 7 => tabS35 0 4 0 3 1 1
  | 8 => tabS35 0 4 0 4 0 0
  | 9 => tabS35 0 4 0 4 0 1
  | 10 => tabS35 0 4 0 4 1 0
  | 11 => tabS35 0 4 0 4 1 1
  | 12 => tabS35 0 4 1 0 0 0
  | 13 => tabS35 0 4 1 0 0 1
  | 14 => tabS35 0 4 1 0 1 0
  | 15 => tabS35 0 4 1 0 1 1
  | 16 => tabS35 0 4 1 1 0 0
  | 17 => tabS35 0 4 1 1 0 1
  | 18 => tabS35 0 4 1 1 1 0
  | _ => tabS35 0 4 1 1 1 1
def memRowS3516 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 4 1 2 0 0
  | 1 => tabS35 0 4 1 2 0 1
  | 2 => tabS35 0 4 1 2 1 0
  | 3 => tabS35 0 4 1 2 1 1
  | 4 => tabS35 0 4 1 3 0 0
  | 5 => tabS35 0 4 1 3 0 1
  | 6 => tabS35 0 4 1 3 1 0
  | 7 => tabS35 0 4 1 3 1 1
  | 8 => tabS35 0 4 1 4 0 0
  | 9 => tabS35 0 4 1 4 0 1
  | 10 => tabS35 0 4 1 4 1 0
  | 11 => tabS35 0 4 1 4 1 1
  | 12 => tabS35 0 4 2 0 0 0
  | 13 => tabS35 0 4 2 0 0 1
  | 14 => tabS35 0 4 2 0 1 0
  | 15 => tabS35 0 4 2 0 1 1
  | 16 => tabS35 0 4 2 1 0 0
  | 17 => tabS35 0 4 2 1 0 1
  | 18 => tabS35 0 4 2 1 1 0
  | _ => tabS35 0 4 2 1 1 1
def memRowS3517 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 4 2 2 0 0
  | 1 => tabS35 0 4 2 2 0 1
  | 2 => tabS35 0 4 2 2 1 0
  | 3 => tabS35 0 4 2 2 1 1
  | 4 => tabS35 0 4 2 3 0 0
  | 5 => tabS35 0 4 2 3 0 1
  | 6 => tabS35 0 4 2 3 1 0
  | 7 => tabS35 0 4 2 3 1 1
  | 8 => tabS35 0 4 2 4 0 0
  | 9 => tabS35 0 4 2 4 0 1
  | 10 => tabS35 0 4 2 4 1 0
  | 11 => tabS35 0 4 2 4 1 1
  | 12 => tabS35 0 4 3 0 0 0
  | 13 => tabS35 0 4 3 0 0 1
  | 14 => tabS35 0 4 3 0 1 0
  | 15 => tabS35 0 4 3 0 1 1
  | 16 => tabS35 0 4 3 1 0 0
  | 17 => tabS35 0 4 3 1 0 1
  | 18 => tabS35 0 4 3 1 1 0
  | _ => tabS35 0 4 3 1 1 1
def memRowS3518 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 4 3 2 0 0
  | 1 => tabS35 0 4 3 2 0 1
  | 2 => tabS35 0 4 3 2 1 0
  | 3 => tabS35 0 4 3 2 1 1
  | 4 => tabS35 0 4 3 3 0 0
  | 5 => tabS35 0 4 3 3 0 1
  | 6 => tabS35 0 4 3 3 1 0
  | 7 => tabS35 0 4 3 3 1 1
  | 8 => tabS35 0 4 3 4 0 0
  | 9 => tabS35 0 4 3 4 0 1
  | 10 => tabS35 0 4 3 4 1 0
  | 11 => tabS35 0 4 3 4 1 1
  | 12 => tabS35 0 4 4 0 0 0
  | 13 => tabS35 0 4 4 0 0 1
  | 14 => tabS35 0 4 4 0 1 0
  | 15 => tabS35 0 4 4 0 1 1
  | 16 => tabS35 0 4 4 1 0 0
  | 17 => tabS35 0 4 4 1 0 1
  | 18 => tabS35 0 4 4 1 1 0
  | _ => tabS35 0 4 4 1 1 1
def memRowS3519 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS35 0 4 4 2 0 0
  | 1 => tabS35 0 4 4 2 0 1
  | 2 => tabS35 0 4 4 2 1 0
  | 3 => tabS35 0 4 4 2 1 1
  | 4 => tabS35 0 4 4 3 0 0
  | 5 => tabS35 0 4 4 3 0 1
  | 6 => tabS35 0 4 4 3 1 0
  | 7 => tabS35 0 4 4 3 1 1
  | 8 => tabS35 0 4 4 4 0 0
  | 9 => tabS35 0 4 4 4 0 1
  | 10 => tabS35 0 4 4 4 1 0
  | _ => tabS35 0 4 4 4 1 1
def memS35 (i : Fin 392) : Fin 5 → Fin 5 → Fin 5 :=
  match (i.1 / 20 : Nat) with
  | 0 => memRowS350 ⟨i.1 % 20, by omega⟩
  | 1 => memRowS351 ⟨i.1 % 20, by omega⟩
  | 2 => memRowS352 ⟨i.1 % 20, by omega⟩
  | 3 => memRowS353 ⟨i.1 % 20, by omega⟩
  | 4 => memRowS354 ⟨i.1 % 20, by omega⟩
  | 5 => memRowS355 ⟨i.1 % 20, by omega⟩
  | 6 => memRowS356 ⟨i.1 % 20, by omega⟩
  | 7 => memRowS357 ⟨i.1 % 20, by omega⟩
  | 8 => memRowS358 ⟨i.1 % 20, by omega⟩
  | 9 => memRowS359 ⟨i.1 % 20, by omega⟩
  | 10 => memRowS3510 ⟨i.1 % 20, by omega⟩
  | 11 => memRowS3511 ⟨i.1 % 20, by omega⟩
  | 12 => memRowS3512 ⟨i.1 % 20, by omega⟩
  | 13 => memRowS3513 ⟨i.1 % 20, by omega⟩
  | 14 => memRowS3514 ⟨i.1 % 20, by omega⟩
  | 15 => memRowS3515 ⟨i.1 % 20, by omega⟩
  | 16 => memRowS3516 ⟨i.1 % 20, by omega⟩
  | 17 => memRowS3517 ⟨i.1 % 20, by omega⟩
  | 18 => memRowS3518 ⟨i.1 % 20, by omega⟩
  | _ => memRowS3519 ⟨i.1 % 20, by omega⟩

/-- Which of the `392` members a given invariant tuple is, so that `mem_of_isExactS35` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS35 : Array Nat := #[
  0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16,
  17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
  41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 65, 66, 67,
  68, 69, 70, 71, 0, 0, 0, 0, 0, 0, 0, 0, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
  86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107,
  108, 109, 110, 111, 0, 0, 0, 0, 112, 113, 114, 115, 116, 117, 118, 119, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 120, 121, 122, 123, 124, 125, 126, 127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128,
  129, 130, 131, 132, 133, 134, 135, 0, 0, 0, 0, 0, 0, 0, 0, 136, 137, 138, 139, 140, 141, 142,
  143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161,
  162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 0, 0, 0, 0, 176, 177,
  178, 179, 180, 181, 182, 183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 185, 186, 187, 188, 189,
  190, 191, 0, 0, 0, 0, 0, 0, 0, 0, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
  204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
  223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241,
  242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260,
  261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279,
  280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298,
  299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317,
  318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336,
  337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
  356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374,
  375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391]

/-- The arguments as one mixed-radix index, which is how `rankArrS35` is addressed. -/
def encTS35 (a : Fin 1) (b c d : Fin 5) (e f : Fin 2) : Nat :=
  a.1 * 500 +
    b.1 * 100 +
    c.1 * 20 +
    d.1 * 4 +
    e.1 * 2 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS35 (a : Fin 1) (b c d : Fin 5) (e f : Fin 2) : Fin 392 :=
  ⟨min (rankArrS35.getD (encTS35 a b c d e f) 0) 391, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS35 (i : Fin 392) : Magma (Fin 5) := Magma.mk (memS35 i)

theorem exactS35_isEndo (i : Fin 392) (j : Fin 6) : (exactS35 i).IsEndo ⇑(eES35 j) := by
  simp only [eES35, coe_permOf]; revert i j; native_decide

theorem exactS35_not_isEndo (i : Fin 392) (j : Fin 2) : ¬ (exactS35 i).IsEndo ⇑(eXS35 j) := by
  simp only [eXS35, coe_permOf]; revert i j; native_decide

/-- `rankS35` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS35` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS35 (a : Fin 1) (b c d : Fin 5) (e f : Fin 2)
    (h : Magma.isExact (tabS35 a b c d e f) permES35 permXS35 = true) :
    memS35 (rankS35 a b c d e f) = tabS35 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `392`
listed members. -/
theorem mem_of_isExactS35 (a : Fin 1) (b c d : Fin 5) (e f : Fin 2)
    (h : Magma.isExact (tabS35 a b c d e f) permES35 permXS35 = true) :
    ∃ i, memS35 i = tabS35 a b c d e f :=
  ⟨_, mem_rankS35 a b c d e f h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS35`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS35` turns that into a member index. -/
theorem exists_exactS35 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eES35 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS35 i)) : ∃ i, exactS35 i = M := by
  simp only [eES35, coe_permOf] at hE
  simp only [eXS35, coe_permOf] at hX
  have hop : M.op = Magma.transport permES35 trS35 (fun i ↦ M.op (repS35 i).1 (repS35 i).2) :=
    Magma.op_eq_transport (rep := repS35) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES35) (idx := stabIdxS350) (a := (repS35 0).1) (b := (repS35 0).2)
    (val := valS350) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES35) (idx := stabIdxS351) (a := (repS35 1).1) (b := (repS35 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES35) (idx := stabIdxS352) (a := (repS35 2).1) (b := (repS35 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES35) (idx := stabIdxS353) (a := (repS35 3).1) (b := (repS35 3).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES35) (idx := stabIdxS354) (a := (repS35 4).1) (b := (repS35 4).2)
    (val := valS354) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permES35) (idx := stabIdxS355) (a := (repS35 5).1) (b := (repS35 5).2)
    (val := valS355) hE (by decide) (by decide)
  have hdec : decS35 a b c d e f = fun i ↦ M.op (repS35 i).1 (repS35 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabS35 a b c d e f = M.op := by
    rw [tabS35_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS35 a b c d e f) permES35 permXS35 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS35 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`6` group of `Magma.permES35`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS35 {L L' : Law.NatMagmaLaw} {i : Fin 392}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactS35 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactS35 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS35 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS35
    (fun k ↦ (Magma.exactS35_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS35_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
