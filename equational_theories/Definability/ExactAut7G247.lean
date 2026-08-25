import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `G247` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 1)(2 3)(4 5 6), (0 2)(1 3)(5 6), (0 2 1 3)(5 6)⟩` -/

/-- The `24` elements of the group: `()`, `(4 5 6)`, `(4 6 5)`, `(2 3)`, `(2 3)(4 5 6)`, `(2 3)(4 6
5)`, `(0 1)`, `(0 1)(4 5 6)`, `(0 1)(4 6 5)`, `(0 1)(2 3)`, `(0 1)(2 3)(4 5 6)`, `(0 1)(2 3)(4 6
5)`, `(0 2)(1 3)(5 6)`, `(0 2)(1 3)(4 5)`, `(0 2)(1 3)(4 6)`, `(0 2 1 3)(5 6)`, `(0 2 1 3)(4 5)`,
`(0 2 1 3)(4 6)`, `(0 3 1 2)(5 6)`, `(0 3 1 2)(4 5)`, `(0 3 1 2)(4 6)`, `(0 3)(1 2)(5 6)`, `(0 3)(1
2)(4 5)`, `(0 3)(1 2)(4 6)`. -/
def pEG2470 : Fin 7 → Fin 7 := id
def pEG2471 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 4
def pEG2472 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 4 | 6 => 5
def pEG2473 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6
def pEG2474 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4
def pEG2475 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5
def pEG2476 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6
def pEG2477 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 4
def pEG2478 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 4 | 6 => 5
def pEG2479 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6
def pEG24710 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4
def pEG24711 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5
def pEG24712 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5
def pEG24713 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6
def pEG24714 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4
def pEG24715 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5
def pEG24716 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 6
def pEG24717 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4
def pEG24718 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5
def pEG24719 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6
def pEG24720 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4
def pEG24721 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5
def pEG24722 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 6
def pEG24723 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4

def permEG247 : Fin 24 → Fin 7 → Fin 7
  | 0 => pEG2470
  | 1 => pEG2471
  | 2 => pEG2472
  | 3 => pEG2473
  | 4 => pEG2474
  | 5 => pEG2475
  | 6 => pEG2476
  | 7 => pEG2477
  | 8 => pEG2478
  | 9 => pEG2479
  | 10 => pEG24710
  | 11 => pEG24711
  | 12 => pEG24712
  | 13 => pEG24713
  | 14 => pEG24714
  | 15 => pEG24715
  | 16 => pEG24716
  | 17 => pEG24717
  | 18 => pEG24718
  | 19 => pEG24719
  | 20 => pEG24720
  | 21 => pEG24721
  | 22 => pEG24722
  | _ => pEG24723

def permEinvG247 : Fin 24 → Fin 7 → Fin 7
  | 0 => pEG2470
  | 1 => pEG2472
  | 2 => pEG2471
  | 3 => pEG2473
  | 4 => pEG2475
  | 5 => pEG2474
  | 6 => pEG2476
  | 7 => pEG2478
  | 8 => pEG2477
  | 9 => pEG2479
  | 10 => pEG24711
  | 11 => pEG24710
  | 12 => pEG24712
  | 13 => pEG24713
  | 14 => pEG24714
  | 15 => pEG24718
  | 16 => pEG24719
  | 17 => pEG24720
  | 18 => pEG24715
  | 19 => pEG24716
  | 20 => pEG24717
  | 21 => pEG24721
  | 22 => pEG24722
  | _ => pEG24723

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEG247 (i : Fin 24) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permEG247 i) (permEinvG247 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 2 1 3)(4 5 6)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXG2470 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 6 | 6 => 4
def pXG2470inv : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 5

def permXG247 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXG2470

def permXinvG247 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXG2470inv

def eXG247 (i : Fin 1) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXG247 i) (permXinvG247 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `7`, so an invariant
operation is `7` values. -/
def repG247 : Fin 7 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (4, 0)
  | 5 => (4, 4)
  | 6 => (4, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trG247 : Fin 7 → Fin 7 → Fin 7 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 3)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 0, 6 => (3, 2)
  | 1, 0 => (1, 6)
  | 1, 1 => (0, 6)
  | 1, 2 => (2, 6)
  | 1, 3 => (2, 9)
  | 1, 4 => (3, 6)
  | 1, 5 => (3, 7)
  | 1, 6 => (3, 8)
  | 2, 0 => (2, 12)
  | 2, 1 => (2, 15)
  | 2, 2 => (0, 12)
  | 2, 3 => (1, 12)
  | 2, 4 => (3, 12)
  | 2, 5 => (3, 13)
  | 2, 6 => (3, 14)
  | 3, 0 => (2, 18)
  | 3, 1 => (2, 21)
  | 3, 2 => (1, 18)
  | 3, 3 => (0, 18)
  | 3, 4 => (3, 18)
  | 3, 5 => (3, 19)
  | 3, 6 => (3, 20)
  | 4, 0 => (4, 0)
  | 4, 1 => (4, 6)
  | 4, 2 => (4, 12)
  | 4, 3 => (4, 18)
  | 4, 4 => (5, 0)
  | 4, 5 => (6, 0)
  | 4, 6 => (6, 12)
  | 5, 0 => (4, 1)
  | 5, 1 => (4, 7)
  | 5, 2 => (4, 13)
  | 5, 3 => (4, 19)
  | 5, 4 => (6, 13)
  | 5, 5 => (5, 1)
  | 5, 6 => (6, 1)
  | 6, 0 => (4, 2)
  | 6, 1 => (4, 8)
  | 6, 2 => (4, 14)
  | 6, 3 => (4, 20)
  | 6, 4 => (6, 2)
  | 6, 5 => (6, 14)
  | 6, 6 => (5, 2)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxG2470 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valG2470 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxG2471 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valG2471 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 1

/-- The `3` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdxG2472 : Fin 3 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valG2472 : Fin 4 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, `4`, `5`, `6`, so the orbit is indexed by `Fin 5`
instead. -/
def stabIdxG2473 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 3
def valG2473 : Fin 5 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 6

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `4`, `5`, `6`, so the orbit is indexed by `Fin 5`
instead. -/
def stabIdxG2474 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 3
def valG2474 : Fin 5 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 6

/-- The `8` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `4`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxG2475 : Fin 8 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 6
  | 3 => 9
  | 4 => 12
  | 5 => 15
  | 6 => 18
  | 7 => 21
def valG2475 : Fin 1 → Fin 7
  | 0 => 4

/-- The `4` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `4`, `5`, `6`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxG2476 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 6
  | 3 => 9
def valG2476 : Fin 3 → Fin 7
  | 0 => 4
  | 1 => 5
  | 2 => 6

/-- The `7` orbit values named by the family's arguments. -/
def decG247 (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Fin 7 → Fin 7
  | 0 => valG2470 a
  | 1 => valG2471 b
  | 2 => valG2472 c
  | 3 => valG2473 d
  | 4 => valG2474 e
  | 5 => valG2475 f
  | 6 => valG2476 g

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabG247_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabG247 (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valG2470 a
  | 0, 1 => valG2471 b
  | 0, 2 => valG2472 c
  | 0, 3 => pEG2473 (valG2472 c)
  | 0, 4 => valG2473 d
  | 0, 5 => pEG2471 (valG2473 d)
  | 0, 6 => pEG2472 (valG2473 d)
  | 1, 0 => pEG2476 (valG2471 b)
  | 1, 1 => pEG2476 (valG2470 a)
  | 1, 2 => pEG2476 (valG2472 c)
  | 1, 3 => pEG2479 (valG2472 c)
  | 1, 4 => pEG2476 (valG2473 d)
  | 1, 5 => pEG2477 (valG2473 d)
  | 1, 6 => pEG2478 (valG2473 d)
  | 2, 0 => pEG24712 (valG2472 c)
  | 2, 1 => pEG24715 (valG2472 c)
  | 2, 2 => pEG24712 (valG2470 a)
  | 2, 3 => pEG24712 (valG2471 b)
  | 2, 4 => pEG24712 (valG2473 d)
  | 2, 5 => pEG24713 (valG2473 d)
  | 2, 6 => pEG24714 (valG2473 d)
  | 3, 0 => pEG24718 (valG2472 c)
  | 3, 1 => pEG24721 (valG2472 c)
  | 3, 2 => pEG24718 (valG2471 b)
  | 3, 3 => pEG24718 (valG2470 a)
  | 3, 4 => pEG24718 (valG2473 d)
  | 3, 5 => pEG24719 (valG2473 d)
  | 3, 6 => pEG24720 (valG2473 d)
  | 4, 0 => valG2474 e
  | 4, 1 => pEG2476 (valG2474 e)
  | 4, 2 => pEG24712 (valG2474 e)
  | 4, 3 => pEG24718 (valG2474 e)
  | 4, 4 => valG2475 f
  | 4, 5 => valG2476 g
  | 4, 6 => pEG24712 (valG2476 g)
  | 5, 0 => pEG2471 (valG2474 e)
  | 5, 1 => pEG2477 (valG2474 e)
  | 5, 2 => pEG24713 (valG2474 e)
  | 5, 3 => pEG24719 (valG2474 e)
  | 5, 4 => pEG24713 (valG2476 g)
  | 5, 5 => pEG2471 (valG2475 f)
  | 5, 6 => pEG2471 (valG2476 g)
  | 6, 0 => pEG2472 (valG2474 e)
  | 6, 1 => pEG2478 (valG2474 e)
  | 6, 2 => pEG24714 (valG2474 e)
  | 6, 3 => pEG24720 (valG2474 e)
  | 6, 4 => pEG2472 (valG2476 g)
  | 6, 5 => pEG24714 (valG2476 g)
  | 6, 6 => pEG2472 (valG2475 f)

theorem tabG247_eq_transport (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) :
    tabG247 a b c d e f g = Magma.transport permEG247 trG247 (decG247 a b c d e f g) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `768` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `1200` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowG2470 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 0 0 3 0 0
  | 1 => tabG247 0 0 0 0 3 0 1
  | 2 => tabG247 0 0 0 0 3 0 2
  | 3 => tabG247 0 0 0 0 4 0 0
  | 4 => tabG247 0 0 0 0 4 0 1
  | 5 => tabG247 0 0 0 0 4 0 2
  | 6 => tabG247 0 0 0 1 3 0 0
  | 7 => tabG247 0 0 0 1 3 0 1
  | 8 => tabG247 0 0 0 1 3 0 2
  | 9 => tabG247 0 0 0 1 4 0 0
  | 10 => tabG247 0 0 0 1 4 0 1
  | 11 => tabG247 0 0 0 1 4 0 2
  | 12 => tabG247 0 0 0 2 3 0 0
  | 13 => tabG247 0 0 0 2 3 0 1
  | 14 => tabG247 0 0 0 2 3 0 2
  | 15 => tabG247 0 0 0 2 4 0 0
  | 16 => tabG247 0 0 0 2 4 0 1
  | 17 => tabG247 0 0 0 2 4 0 2
  | 18 => tabG247 0 0 0 3 0 0 0
  | 19 => tabG247 0 0 0 3 0 0 1
  | 20 => tabG247 0 0 0 3 0 0 2
  | 21 => tabG247 0 0 0 3 1 0 0
  | 22 => tabG247 0 0 0 3 1 0 1
  | 23 => tabG247 0 0 0 3 1 0 2
  | 24 => tabG247 0 0 0 3 2 0 0
  | 25 => tabG247 0 0 0 3 2 0 1
  | 26 => tabG247 0 0 0 3 2 0 2
  | _ => tabG247 0 0 0 3 3 0 0
def memRowG2471 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 0 3 3 0 1
  | 1 => tabG247 0 0 0 3 3 0 2
  | 2 => tabG247 0 0 0 3 4 0 0
  | 3 => tabG247 0 0 0 3 4 0 1
  | 4 => tabG247 0 0 0 3 4 0 2
  | 5 => tabG247 0 0 0 4 0 0 0
  | 6 => tabG247 0 0 0 4 0 0 1
  | 7 => tabG247 0 0 0 4 0 0 2
  | 8 => tabG247 0 0 0 4 1 0 0
  | 9 => tabG247 0 0 0 4 1 0 1
  | 10 => tabG247 0 0 0 4 1 0 2
  | 11 => tabG247 0 0 0 4 2 0 0
  | 12 => tabG247 0 0 0 4 2 0 1
  | 13 => tabG247 0 0 0 4 2 0 2
  | 14 => tabG247 0 0 0 4 3 0 0
  | 15 => tabG247 0 0 0 4 3 0 1
  | 16 => tabG247 0 0 0 4 3 0 2
  | 17 => tabG247 0 0 0 4 4 0 0
  | 18 => tabG247 0 0 0 4 4 0 1
  | 19 => tabG247 0 0 0 4 4 0 2
  | 20 => tabG247 0 0 1 0 3 0 0
  | 21 => tabG247 0 0 1 0 3 0 1
  | 22 => tabG247 0 0 1 0 3 0 2
  | 23 => tabG247 0 0 1 0 4 0 0
  | 24 => tabG247 0 0 1 0 4 0 1
  | 25 => tabG247 0 0 1 0 4 0 2
  | 26 => tabG247 0 0 1 1 3 0 0
  | _ => tabG247 0 0 1 1 3 0 1
def memRowG2472 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 1 1 3 0 2
  | 1 => tabG247 0 0 1 1 4 0 0
  | 2 => tabG247 0 0 1 1 4 0 1
  | 3 => tabG247 0 0 1 1 4 0 2
  | 4 => tabG247 0 0 1 2 3 0 0
  | 5 => tabG247 0 0 1 2 3 0 1
  | 6 => tabG247 0 0 1 2 3 0 2
  | 7 => tabG247 0 0 1 2 4 0 0
  | 8 => tabG247 0 0 1 2 4 0 1
  | 9 => tabG247 0 0 1 2 4 0 2
  | 10 => tabG247 0 0 1 3 0 0 0
  | 11 => tabG247 0 0 1 3 0 0 1
  | 12 => tabG247 0 0 1 3 0 0 2
  | 13 => tabG247 0 0 1 3 1 0 0
  | 14 => tabG247 0 0 1 3 1 0 1
  | 15 => tabG247 0 0 1 3 1 0 2
  | 16 => tabG247 0 0 1 3 2 0 0
  | 17 => tabG247 0 0 1 3 2 0 1
  | 18 => tabG247 0 0 1 3 2 0 2
  | 19 => tabG247 0 0 1 3 3 0 0
  | 20 => tabG247 0 0 1 3 3 0 1
  | 21 => tabG247 0 0 1 3 3 0 2
  | 22 => tabG247 0 0 1 3 4 0 0
  | 23 => tabG247 0 0 1 3 4 0 1
  | 24 => tabG247 0 0 1 3 4 0 2
  | 25 => tabG247 0 0 1 4 0 0 0
  | 26 => tabG247 0 0 1 4 0 0 1
  | _ => tabG247 0 0 1 4 0 0 2
def memRowG2473 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 1 4 1 0 0
  | 1 => tabG247 0 0 1 4 1 0 1
  | 2 => tabG247 0 0 1 4 1 0 2
  | 3 => tabG247 0 0 1 4 2 0 0
  | 4 => tabG247 0 0 1 4 2 0 1
  | 5 => tabG247 0 0 1 4 2 0 2
  | 6 => tabG247 0 0 1 4 3 0 0
  | 7 => tabG247 0 0 1 4 3 0 1
  | 8 => tabG247 0 0 1 4 3 0 2
  | 9 => tabG247 0 0 1 4 4 0 0
  | 10 => tabG247 0 0 1 4 4 0 1
  | 11 => tabG247 0 0 1 4 4 0 2
  | 12 => tabG247 0 0 2 0 3 0 0
  | 13 => tabG247 0 0 2 0 3 0 1
  | 14 => tabG247 0 0 2 0 3 0 2
  | 15 => tabG247 0 0 2 0 4 0 0
  | 16 => tabG247 0 0 2 0 4 0 1
  | 17 => tabG247 0 0 2 0 4 0 2
  | 18 => tabG247 0 0 2 1 3 0 0
  | 19 => tabG247 0 0 2 1 3 0 1
  | 20 => tabG247 0 0 2 1 3 0 2
  | 21 => tabG247 0 0 2 1 4 0 0
  | 22 => tabG247 0 0 2 1 4 0 1
  | 23 => tabG247 0 0 2 1 4 0 2
  | 24 => tabG247 0 0 2 2 3 0 0
  | 25 => tabG247 0 0 2 2 3 0 1
  | 26 => tabG247 0 0 2 2 3 0 2
  | _ => tabG247 0 0 2 2 4 0 0
def memRowG2474 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 2 2 4 0 1
  | 1 => tabG247 0 0 2 2 4 0 2
  | 2 => tabG247 0 0 2 3 0 0 0
  | 3 => tabG247 0 0 2 3 0 0 1
  | 4 => tabG247 0 0 2 3 0 0 2
  | 5 => tabG247 0 0 2 3 1 0 0
  | 6 => tabG247 0 0 2 3 1 0 1
  | 7 => tabG247 0 0 2 3 1 0 2
  | 8 => tabG247 0 0 2 3 2 0 0
  | 9 => tabG247 0 0 2 3 2 0 1
  | 10 => tabG247 0 0 2 3 2 0 2
  | 11 => tabG247 0 0 2 3 3 0 0
  | 12 => tabG247 0 0 2 3 3 0 1
  | 13 => tabG247 0 0 2 3 3 0 2
  | 14 => tabG247 0 0 2 3 4 0 0
  | 15 => tabG247 0 0 2 3 4 0 1
  | 16 => tabG247 0 0 2 3 4 0 2
  | 17 => tabG247 0 0 2 4 0 0 0
  | 18 => tabG247 0 0 2 4 0 0 1
  | 19 => tabG247 0 0 2 4 0 0 2
  | 20 => tabG247 0 0 2 4 1 0 0
  | 21 => tabG247 0 0 2 4 1 0 1
  | 22 => tabG247 0 0 2 4 1 0 2
  | 23 => tabG247 0 0 2 4 2 0 0
  | 24 => tabG247 0 0 2 4 2 0 1
  | 25 => tabG247 0 0 2 4 2 0 2
  | 26 => tabG247 0 0 2 4 3 0 0
  | _ => tabG247 0 0 2 4 3 0 1
def memRowG2475 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 2 4 3 0 2
  | 1 => tabG247 0 0 2 4 4 0 0
  | 2 => tabG247 0 0 2 4 4 0 1
  | 3 => tabG247 0 0 2 4 4 0 2
  | 4 => tabG247 0 0 3 0 3 0 0
  | 5 => tabG247 0 0 3 0 3 0 1
  | 6 => tabG247 0 0 3 0 3 0 2
  | 7 => tabG247 0 0 3 0 4 0 0
  | 8 => tabG247 0 0 3 0 4 0 1
  | 9 => tabG247 0 0 3 0 4 0 2
  | 10 => tabG247 0 0 3 1 3 0 0
  | 11 => tabG247 0 0 3 1 3 0 1
  | 12 => tabG247 0 0 3 1 3 0 2
  | 13 => tabG247 0 0 3 1 4 0 0
  | 14 => tabG247 0 0 3 1 4 0 1
  | 15 => tabG247 0 0 3 1 4 0 2
  | 16 => tabG247 0 0 3 2 3 0 0
  | 17 => tabG247 0 0 3 2 3 0 1
  | 18 => tabG247 0 0 3 2 3 0 2
  | 19 => tabG247 0 0 3 2 4 0 0
  | 20 => tabG247 0 0 3 2 4 0 1
  | 21 => tabG247 0 0 3 2 4 0 2
  | 22 => tabG247 0 0 3 3 0 0 0
  | 23 => tabG247 0 0 3 3 0 0 1
  | 24 => tabG247 0 0 3 3 0 0 2
  | 25 => tabG247 0 0 3 3 1 0 0
  | 26 => tabG247 0 0 3 3 1 0 1
  | _ => tabG247 0 0 3 3 1 0 2
def memRowG2476 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 0 3 3 2 0 0
  | 1 => tabG247 0 0 3 3 2 0 1
  | 2 => tabG247 0 0 3 3 2 0 2
  | 3 => tabG247 0 0 3 3 3 0 0
  | 4 => tabG247 0 0 3 3 3 0 1
  | 5 => tabG247 0 0 3 3 3 0 2
  | 6 => tabG247 0 0 3 3 4 0 0
  | 7 => tabG247 0 0 3 3 4 0 1
  | 8 => tabG247 0 0 3 3 4 0 2
  | 9 => tabG247 0 0 3 4 0 0 0
  | 10 => tabG247 0 0 3 4 0 0 1
  | 11 => tabG247 0 0 3 4 0 0 2
  | 12 => tabG247 0 0 3 4 1 0 0
  | 13 => tabG247 0 0 3 4 1 0 1
  | 14 => tabG247 0 0 3 4 1 0 2
  | 15 => tabG247 0 0 3 4 2 0 0
  | 16 => tabG247 0 0 3 4 2 0 1
  | 17 => tabG247 0 0 3 4 2 0 2
  | 18 => tabG247 0 0 3 4 3 0 0
  | 19 => tabG247 0 0 3 4 3 0 1
  | 20 => tabG247 0 0 3 4 3 0 2
  | 21 => tabG247 0 0 3 4 4 0 0
  | 22 => tabG247 0 0 3 4 4 0 1
  | 23 => tabG247 0 0 3 4 4 0 2
  | 24 => tabG247 0 1 0 0 3 0 0
  | 25 => tabG247 0 1 0 0 3 0 1
  | 26 => tabG247 0 1 0 0 3 0 2
  | _ => tabG247 0 1 0 0 4 0 0
def memRowG2477 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 0 0 4 0 1
  | 1 => tabG247 0 1 0 0 4 0 2
  | 2 => tabG247 0 1 0 1 3 0 0
  | 3 => tabG247 0 1 0 1 3 0 1
  | 4 => tabG247 0 1 0 1 3 0 2
  | 5 => tabG247 0 1 0 1 4 0 0
  | 6 => tabG247 0 1 0 1 4 0 1
  | 7 => tabG247 0 1 0 1 4 0 2
  | 8 => tabG247 0 1 0 2 3 0 0
  | 9 => tabG247 0 1 0 2 3 0 1
  | 10 => tabG247 0 1 0 2 3 0 2
  | 11 => tabG247 0 1 0 2 4 0 0
  | 12 => tabG247 0 1 0 2 4 0 1
  | 13 => tabG247 0 1 0 2 4 0 2
  | 14 => tabG247 0 1 0 3 0 0 0
  | 15 => tabG247 0 1 0 3 0 0 1
  | 16 => tabG247 0 1 0 3 0 0 2
  | 17 => tabG247 0 1 0 3 1 0 0
  | 18 => tabG247 0 1 0 3 1 0 1
  | 19 => tabG247 0 1 0 3 1 0 2
  | 20 => tabG247 0 1 0 3 2 0 0
  | 21 => tabG247 0 1 0 3 2 0 1
  | 22 => tabG247 0 1 0 3 2 0 2
  | 23 => tabG247 0 1 0 3 3 0 0
  | 24 => tabG247 0 1 0 3 3 0 1
  | 25 => tabG247 0 1 0 3 3 0 2
  | 26 => tabG247 0 1 0 3 4 0 0
  | _ => tabG247 0 1 0 3 4 0 1
def memRowG2478 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 0 3 4 0 2
  | 1 => tabG247 0 1 0 4 0 0 0
  | 2 => tabG247 0 1 0 4 0 0 1
  | 3 => tabG247 0 1 0 4 0 0 2
  | 4 => tabG247 0 1 0 4 1 0 0
  | 5 => tabG247 0 1 0 4 1 0 1
  | 6 => tabG247 0 1 0 4 1 0 2
  | 7 => tabG247 0 1 0 4 2 0 0
  | 8 => tabG247 0 1 0 4 2 0 1
  | 9 => tabG247 0 1 0 4 2 0 2
  | 10 => tabG247 0 1 0 4 3 0 0
  | 11 => tabG247 0 1 0 4 3 0 1
  | 12 => tabG247 0 1 0 4 3 0 2
  | 13 => tabG247 0 1 0 4 4 0 0
  | 14 => tabG247 0 1 0 4 4 0 1
  | 15 => tabG247 0 1 0 4 4 0 2
  | 16 => tabG247 0 1 1 0 3 0 0
  | 17 => tabG247 0 1 1 0 3 0 1
  | 18 => tabG247 0 1 1 0 3 0 2
  | 19 => tabG247 0 1 1 0 4 0 0
  | 20 => tabG247 0 1 1 0 4 0 1
  | 21 => tabG247 0 1 1 0 4 0 2
  | 22 => tabG247 0 1 1 1 3 0 0
  | 23 => tabG247 0 1 1 1 3 0 1
  | 24 => tabG247 0 1 1 1 3 0 2
  | 25 => tabG247 0 1 1 1 4 0 0
  | 26 => tabG247 0 1 1 1 4 0 1
  | _ => tabG247 0 1 1 1 4 0 2
def memRowG2479 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 1 2 3 0 0
  | 1 => tabG247 0 1 1 2 3 0 1
  | 2 => tabG247 0 1 1 2 3 0 2
  | 3 => tabG247 0 1 1 2 4 0 0
  | 4 => tabG247 0 1 1 2 4 0 1
  | 5 => tabG247 0 1 1 2 4 0 2
  | 6 => tabG247 0 1 1 3 0 0 0
  | 7 => tabG247 0 1 1 3 0 0 1
  | 8 => tabG247 0 1 1 3 0 0 2
  | 9 => tabG247 0 1 1 3 1 0 0
  | 10 => tabG247 0 1 1 3 1 0 1
  | 11 => tabG247 0 1 1 3 1 0 2
  | 12 => tabG247 0 1 1 3 2 0 0
  | 13 => tabG247 0 1 1 3 2 0 1
  | 14 => tabG247 0 1 1 3 2 0 2
  | 15 => tabG247 0 1 1 3 3 0 0
  | 16 => tabG247 0 1 1 3 3 0 1
  | 17 => tabG247 0 1 1 3 3 0 2
  | 18 => tabG247 0 1 1 3 4 0 0
  | 19 => tabG247 0 1 1 3 4 0 1
  | 20 => tabG247 0 1 1 3 4 0 2
  | 21 => tabG247 0 1 1 4 0 0 0
  | 22 => tabG247 0 1 1 4 0 0 1
  | 23 => tabG247 0 1 1 4 0 0 2
  | 24 => tabG247 0 1 1 4 1 0 0
  | 25 => tabG247 0 1 1 4 1 0 1
  | 26 => tabG247 0 1 1 4 1 0 2
  | _ => tabG247 0 1 1 4 2 0 0
def memRowG24710 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 1 4 2 0 1
  | 1 => tabG247 0 1 1 4 2 0 2
  | 2 => tabG247 0 1 1 4 3 0 0
  | 3 => tabG247 0 1 1 4 3 0 1
  | 4 => tabG247 0 1 1 4 3 0 2
  | 5 => tabG247 0 1 1 4 4 0 0
  | 6 => tabG247 0 1 1 4 4 0 1
  | 7 => tabG247 0 1 1 4 4 0 2
  | 8 => tabG247 0 1 2 0 3 0 0
  | 9 => tabG247 0 1 2 0 3 0 1
  | 10 => tabG247 0 1 2 0 3 0 2
  | 11 => tabG247 0 1 2 0 4 0 0
  | 12 => tabG247 0 1 2 0 4 0 1
  | 13 => tabG247 0 1 2 0 4 0 2
  | 14 => tabG247 0 1 2 1 3 0 0
  | 15 => tabG247 0 1 2 1 3 0 1
  | 16 => tabG247 0 1 2 1 3 0 2
  | 17 => tabG247 0 1 2 1 4 0 0
  | 18 => tabG247 0 1 2 1 4 0 1
  | 19 => tabG247 0 1 2 1 4 0 2
  | 20 => tabG247 0 1 2 2 3 0 0
  | 21 => tabG247 0 1 2 2 3 0 1
  | 22 => tabG247 0 1 2 2 3 0 2
  | 23 => tabG247 0 1 2 2 4 0 0
  | 24 => tabG247 0 1 2 2 4 0 1
  | 25 => tabG247 0 1 2 2 4 0 2
  | 26 => tabG247 0 1 2 3 0 0 0
  | _ => tabG247 0 1 2 3 0 0 1
def memRowG24711 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 2 3 0 0 2
  | 1 => tabG247 0 1 2 3 1 0 0
  | 2 => tabG247 0 1 2 3 1 0 1
  | 3 => tabG247 0 1 2 3 1 0 2
  | 4 => tabG247 0 1 2 3 2 0 0
  | 5 => tabG247 0 1 2 3 2 0 1
  | 6 => tabG247 0 1 2 3 2 0 2
  | 7 => tabG247 0 1 2 3 3 0 0
  | 8 => tabG247 0 1 2 3 3 0 1
  | 9 => tabG247 0 1 2 3 3 0 2
  | 10 => tabG247 0 1 2 3 4 0 0
  | 11 => tabG247 0 1 2 3 4 0 1
  | 12 => tabG247 0 1 2 3 4 0 2
  | 13 => tabG247 0 1 2 4 0 0 0
  | 14 => tabG247 0 1 2 4 0 0 1
  | 15 => tabG247 0 1 2 4 0 0 2
  | 16 => tabG247 0 1 2 4 1 0 0
  | 17 => tabG247 0 1 2 4 1 0 1
  | 18 => tabG247 0 1 2 4 1 0 2
  | 19 => tabG247 0 1 2 4 2 0 0
  | 20 => tabG247 0 1 2 4 2 0 1
  | 21 => tabG247 0 1 2 4 2 0 2
  | 22 => tabG247 0 1 2 4 3 0 0
  | 23 => tabG247 0 1 2 4 3 0 1
  | 24 => tabG247 0 1 2 4 3 0 2
  | 25 => tabG247 0 1 2 4 4 0 0
  | 26 => tabG247 0 1 2 4 4 0 1
  | _ => tabG247 0 1 2 4 4 0 2
def memRowG24712 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 3 0 3 0 0
  | 1 => tabG247 0 1 3 0 3 0 1
  | 2 => tabG247 0 1 3 0 3 0 2
  | 3 => tabG247 0 1 3 0 4 0 0
  | 4 => tabG247 0 1 3 0 4 0 1
  | 5 => tabG247 0 1 3 0 4 0 2
  | 6 => tabG247 0 1 3 1 3 0 0
  | 7 => tabG247 0 1 3 1 3 0 1
  | 8 => tabG247 0 1 3 1 3 0 2
  | 9 => tabG247 0 1 3 1 4 0 0
  | 10 => tabG247 0 1 3 1 4 0 1
  | 11 => tabG247 0 1 3 1 4 0 2
  | 12 => tabG247 0 1 3 2 3 0 0
  | 13 => tabG247 0 1 3 2 3 0 1
  | 14 => tabG247 0 1 3 2 3 0 2
  | 15 => tabG247 0 1 3 2 4 0 0
  | 16 => tabG247 0 1 3 2 4 0 1
  | 17 => tabG247 0 1 3 2 4 0 2
  | 18 => tabG247 0 1 3 3 0 0 0
  | 19 => tabG247 0 1 3 3 0 0 1
  | 20 => tabG247 0 1 3 3 0 0 2
  | 21 => tabG247 0 1 3 3 1 0 0
  | 22 => tabG247 0 1 3 3 1 0 1
  | 23 => tabG247 0 1 3 3 1 0 2
  | 24 => tabG247 0 1 3 3 2 0 0
  | 25 => tabG247 0 1 3 3 2 0 1
  | 26 => tabG247 0 1 3 3 2 0 2
  | _ => tabG247 0 1 3 3 3 0 0
def memRowG24713 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 0 1 3 3 3 0 1
  | 1 => tabG247 0 1 3 3 3 0 2
  | 2 => tabG247 0 1 3 3 4 0 0
  | 3 => tabG247 0 1 3 3 4 0 1
  | 4 => tabG247 0 1 3 3 4 0 2
  | 5 => tabG247 0 1 3 4 0 0 0
  | 6 => tabG247 0 1 3 4 0 0 1
  | 7 => tabG247 0 1 3 4 0 0 2
  | 8 => tabG247 0 1 3 4 1 0 0
  | 9 => tabG247 0 1 3 4 1 0 1
  | 10 => tabG247 0 1 3 4 1 0 2
  | 11 => tabG247 0 1 3 4 2 0 0
  | 12 => tabG247 0 1 3 4 2 0 1
  | 13 => tabG247 0 1 3 4 2 0 2
  | 14 => tabG247 0 1 3 4 3 0 0
  | 15 => tabG247 0 1 3 4 3 0 1
  | 16 => tabG247 0 1 3 4 3 0 2
  | 17 => tabG247 0 1 3 4 4 0 0
  | 18 => tabG247 0 1 3 4 4 0 1
  | 19 => tabG247 0 1 3 4 4 0 2
  | 20 => tabG247 1 0 0 0 3 0 0
  | 21 => tabG247 1 0 0 0 3 0 1
  | 22 => tabG247 1 0 0 0 3 0 2
  | 23 => tabG247 1 0 0 0 4 0 0
  | 24 => tabG247 1 0 0 0 4 0 1
  | 25 => tabG247 1 0 0 0 4 0 2
  | 26 => tabG247 1 0 0 1 3 0 0
  | _ => tabG247 1 0 0 1 3 0 1
def memRowG24714 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 0 1 3 0 2
  | 1 => tabG247 1 0 0 1 4 0 0
  | 2 => tabG247 1 0 0 1 4 0 1
  | 3 => tabG247 1 0 0 1 4 0 2
  | 4 => tabG247 1 0 0 2 3 0 0
  | 5 => tabG247 1 0 0 2 3 0 1
  | 6 => tabG247 1 0 0 2 3 0 2
  | 7 => tabG247 1 0 0 2 4 0 0
  | 8 => tabG247 1 0 0 2 4 0 1
  | 9 => tabG247 1 0 0 2 4 0 2
  | 10 => tabG247 1 0 0 3 0 0 0
  | 11 => tabG247 1 0 0 3 0 0 1
  | 12 => tabG247 1 0 0 3 0 0 2
  | 13 => tabG247 1 0 0 3 1 0 0
  | 14 => tabG247 1 0 0 3 1 0 1
  | 15 => tabG247 1 0 0 3 1 0 2
  | 16 => tabG247 1 0 0 3 2 0 0
  | 17 => tabG247 1 0 0 3 2 0 1
  | 18 => tabG247 1 0 0 3 2 0 2
  | 19 => tabG247 1 0 0 3 3 0 0
  | 20 => tabG247 1 0 0 3 3 0 1
  | 21 => tabG247 1 0 0 3 3 0 2
  | 22 => tabG247 1 0 0 3 4 0 0
  | 23 => tabG247 1 0 0 3 4 0 1
  | 24 => tabG247 1 0 0 3 4 0 2
  | 25 => tabG247 1 0 0 4 0 0 0
  | 26 => tabG247 1 0 0 4 0 0 1
  | _ => tabG247 1 0 0 4 0 0 2
def memRowG24715 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 0 4 1 0 0
  | 1 => tabG247 1 0 0 4 1 0 1
  | 2 => tabG247 1 0 0 4 1 0 2
  | 3 => tabG247 1 0 0 4 2 0 0
  | 4 => tabG247 1 0 0 4 2 0 1
  | 5 => tabG247 1 0 0 4 2 0 2
  | 6 => tabG247 1 0 0 4 3 0 0
  | 7 => tabG247 1 0 0 4 3 0 1
  | 8 => tabG247 1 0 0 4 3 0 2
  | 9 => tabG247 1 0 0 4 4 0 0
  | 10 => tabG247 1 0 0 4 4 0 1
  | 11 => tabG247 1 0 0 4 4 0 2
  | 12 => tabG247 1 0 1 0 3 0 0
  | 13 => tabG247 1 0 1 0 3 0 1
  | 14 => tabG247 1 0 1 0 3 0 2
  | 15 => tabG247 1 0 1 0 4 0 0
  | 16 => tabG247 1 0 1 0 4 0 1
  | 17 => tabG247 1 0 1 0 4 0 2
  | 18 => tabG247 1 0 1 1 3 0 0
  | 19 => tabG247 1 0 1 1 3 0 1
  | 20 => tabG247 1 0 1 1 3 0 2
  | 21 => tabG247 1 0 1 1 4 0 0
  | 22 => tabG247 1 0 1 1 4 0 1
  | 23 => tabG247 1 0 1 1 4 0 2
  | 24 => tabG247 1 0 1 2 3 0 0
  | 25 => tabG247 1 0 1 2 3 0 1
  | 26 => tabG247 1 0 1 2 3 0 2
  | _ => tabG247 1 0 1 2 4 0 0
def memRowG24716 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 1 2 4 0 1
  | 1 => tabG247 1 0 1 2 4 0 2
  | 2 => tabG247 1 0 1 3 0 0 0
  | 3 => tabG247 1 0 1 3 0 0 1
  | 4 => tabG247 1 0 1 3 0 0 2
  | 5 => tabG247 1 0 1 3 1 0 0
  | 6 => tabG247 1 0 1 3 1 0 1
  | 7 => tabG247 1 0 1 3 1 0 2
  | 8 => tabG247 1 0 1 3 2 0 0
  | 9 => tabG247 1 0 1 3 2 0 1
  | 10 => tabG247 1 0 1 3 2 0 2
  | 11 => tabG247 1 0 1 3 3 0 0
  | 12 => tabG247 1 0 1 3 3 0 1
  | 13 => tabG247 1 0 1 3 3 0 2
  | 14 => tabG247 1 0 1 3 4 0 0
  | 15 => tabG247 1 0 1 3 4 0 1
  | 16 => tabG247 1 0 1 3 4 0 2
  | 17 => tabG247 1 0 1 4 0 0 0
  | 18 => tabG247 1 0 1 4 0 0 1
  | 19 => tabG247 1 0 1 4 0 0 2
  | 20 => tabG247 1 0 1 4 1 0 0
  | 21 => tabG247 1 0 1 4 1 0 1
  | 22 => tabG247 1 0 1 4 1 0 2
  | 23 => tabG247 1 0 1 4 2 0 0
  | 24 => tabG247 1 0 1 4 2 0 1
  | 25 => tabG247 1 0 1 4 2 0 2
  | 26 => tabG247 1 0 1 4 3 0 0
  | _ => tabG247 1 0 1 4 3 0 1
def memRowG24717 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 1 4 3 0 2
  | 1 => tabG247 1 0 1 4 4 0 0
  | 2 => tabG247 1 0 1 4 4 0 1
  | 3 => tabG247 1 0 1 4 4 0 2
  | 4 => tabG247 1 0 2 0 3 0 0
  | 5 => tabG247 1 0 2 0 3 0 1
  | 6 => tabG247 1 0 2 0 3 0 2
  | 7 => tabG247 1 0 2 0 4 0 0
  | 8 => tabG247 1 0 2 0 4 0 1
  | 9 => tabG247 1 0 2 0 4 0 2
  | 10 => tabG247 1 0 2 1 3 0 0
  | 11 => tabG247 1 0 2 1 3 0 1
  | 12 => tabG247 1 0 2 1 3 0 2
  | 13 => tabG247 1 0 2 1 4 0 0
  | 14 => tabG247 1 0 2 1 4 0 1
  | 15 => tabG247 1 0 2 1 4 0 2
  | 16 => tabG247 1 0 2 2 3 0 0
  | 17 => tabG247 1 0 2 2 3 0 1
  | 18 => tabG247 1 0 2 2 3 0 2
  | 19 => tabG247 1 0 2 2 4 0 0
  | 20 => tabG247 1 0 2 2 4 0 1
  | 21 => tabG247 1 0 2 2 4 0 2
  | 22 => tabG247 1 0 2 3 0 0 0
  | 23 => tabG247 1 0 2 3 0 0 1
  | 24 => tabG247 1 0 2 3 0 0 2
  | 25 => tabG247 1 0 2 3 1 0 0
  | 26 => tabG247 1 0 2 3 1 0 1
  | _ => tabG247 1 0 2 3 1 0 2
def memRowG24718 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 2 3 2 0 0
  | 1 => tabG247 1 0 2 3 2 0 1
  | 2 => tabG247 1 0 2 3 2 0 2
  | 3 => tabG247 1 0 2 3 3 0 0
  | 4 => tabG247 1 0 2 3 3 0 1
  | 5 => tabG247 1 0 2 3 3 0 2
  | 6 => tabG247 1 0 2 3 4 0 0
  | 7 => tabG247 1 0 2 3 4 0 1
  | 8 => tabG247 1 0 2 3 4 0 2
  | 9 => tabG247 1 0 2 4 0 0 0
  | 10 => tabG247 1 0 2 4 0 0 1
  | 11 => tabG247 1 0 2 4 0 0 2
  | 12 => tabG247 1 0 2 4 1 0 0
  | 13 => tabG247 1 0 2 4 1 0 1
  | 14 => tabG247 1 0 2 4 1 0 2
  | 15 => tabG247 1 0 2 4 2 0 0
  | 16 => tabG247 1 0 2 4 2 0 1
  | 17 => tabG247 1 0 2 4 2 0 2
  | 18 => tabG247 1 0 2 4 3 0 0
  | 19 => tabG247 1 0 2 4 3 0 1
  | 20 => tabG247 1 0 2 4 3 0 2
  | 21 => tabG247 1 0 2 4 4 0 0
  | 22 => tabG247 1 0 2 4 4 0 1
  | 23 => tabG247 1 0 2 4 4 0 2
  | 24 => tabG247 1 0 3 0 3 0 0
  | 25 => tabG247 1 0 3 0 3 0 1
  | 26 => tabG247 1 0 3 0 3 0 2
  | _ => tabG247 1 0 3 0 4 0 0
def memRowG24719 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 3 0 4 0 1
  | 1 => tabG247 1 0 3 0 4 0 2
  | 2 => tabG247 1 0 3 1 3 0 0
  | 3 => tabG247 1 0 3 1 3 0 1
  | 4 => tabG247 1 0 3 1 3 0 2
  | 5 => tabG247 1 0 3 1 4 0 0
  | 6 => tabG247 1 0 3 1 4 0 1
  | 7 => tabG247 1 0 3 1 4 0 2
  | 8 => tabG247 1 0 3 2 3 0 0
  | 9 => tabG247 1 0 3 2 3 0 1
  | 10 => tabG247 1 0 3 2 3 0 2
  | 11 => tabG247 1 0 3 2 4 0 0
  | 12 => tabG247 1 0 3 2 4 0 1
  | 13 => tabG247 1 0 3 2 4 0 2
  | 14 => tabG247 1 0 3 3 0 0 0
  | 15 => tabG247 1 0 3 3 0 0 1
  | 16 => tabG247 1 0 3 3 0 0 2
  | 17 => tabG247 1 0 3 3 1 0 0
  | 18 => tabG247 1 0 3 3 1 0 1
  | 19 => tabG247 1 0 3 3 1 0 2
  | 20 => tabG247 1 0 3 3 2 0 0
  | 21 => tabG247 1 0 3 3 2 0 1
  | 22 => tabG247 1 0 3 3 2 0 2
  | 23 => tabG247 1 0 3 3 3 0 0
  | 24 => tabG247 1 0 3 3 3 0 1
  | 25 => tabG247 1 0 3 3 3 0 2
  | 26 => tabG247 1 0 3 3 4 0 0
  | _ => tabG247 1 0 3 3 4 0 1
def memRowG24720 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 0 3 3 4 0 2
  | 1 => tabG247 1 0 3 4 0 0 0
  | 2 => tabG247 1 0 3 4 0 0 1
  | 3 => tabG247 1 0 3 4 0 0 2
  | 4 => tabG247 1 0 3 4 1 0 0
  | 5 => tabG247 1 0 3 4 1 0 1
  | 6 => tabG247 1 0 3 4 1 0 2
  | 7 => tabG247 1 0 3 4 2 0 0
  | 8 => tabG247 1 0 3 4 2 0 1
  | 9 => tabG247 1 0 3 4 2 0 2
  | 10 => tabG247 1 0 3 4 3 0 0
  | 11 => tabG247 1 0 3 4 3 0 1
  | 12 => tabG247 1 0 3 4 3 0 2
  | 13 => tabG247 1 0 3 4 4 0 0
  | 14 => tabG247 1 0 3 4 4 0 1
  | 15 => tabG247 1 0 3 4 4 0 2
  | 16 => tabG247 1 1 0 0 3 0 0
  | 17 => tabG247 1 1 0 0 3 0 1
  | 18 => tabG247 1 1 0 0 3 0 2
  | 19 => tabG247 1 1 0 0 4 0 0
  | 20 => tabG247 1 1 0 0 4 0 1
  | 21 => tabG247 1 1 0 0 4 0 2
  | 22 => tabG247 1 1 0 1 3 0 0
  | 23 => tabG247 1 1 0 1 3 0 1
  | 24 => tabG247 1 1 0 1 3 0 2
  | 25 => tabG247 1 1 0 1 4 0 0
  | 26 => tabG247 1 1 0 1 4 0 1
  | _ => tabG247 1 1 0 1 4 0 2
def memRowG24721 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 0 2 3 0 0
  | 1 => tabG247 1 1 0 2 3 0 1
  | 2 => tabG247 1 1 0 2 3 0 2
  | 3 => tabG247 1 1 0 2 4 0 0
  | 4 => tabG247 1 1 0 2 4 0 1
  | 5 => tabG247 1 1 0 2 4 0 2
  | 6 => tabG247 1 1 0 3 0 0 0
  | 7 => tabG247 1 1 0 3 0 0 1
  | 8 => tabG247 1 1 0 3 0 0 2
  | 9 => tabG247 1 1 0 3 1 0 0
  | 10 => tabG247 1 1 0 3 1 0 1
  | 11 => tabG247 1 1 0 3 1 0 2
  | 12 => tabG247 1 1 0 3 2 0 0
  | 13 => tabG247 1 1 0 3 2 0 1
  | 14 => tabG247 1 1 0 3 2 0 2
  | 15 => tabG247 1 1 0 3 3 0 0
  | 16 => tabG247 1 1 0 3 3 0 1
  | 17 => tabG247 1 1 0 3 3 0 2
  | 18 => tabG247 1 1 0 3 4 0 0
  | 19 => tabG247 1 1 0 3 4 0 1
  | 20 => tabG247 1 1 0 3 4 0 2
  | 21 => tabG247 1 1 0 4 0 0 0
  | 22 => tabG247 1 1 0 4 0 0 1
  | 23 => tabG247 1 1 0 4 0 0 2
  | 24 => tabG247 1 1 0 4 1 0 0
  | 25 => tabG247 1 1 0 4 1 0 1
  | 26 => tabG247 1 1 0 4 1 0 2
  | _ => tabG247 1 1 0 4 2 0 0
def memRowG24722 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 0 4 2 0 1
  | 1 => tabG247 1 1 0 4 2 0 2
  | 2 => tabG247 1 1 0 4 3 0 0
  | 3 => tabG247 1 1 0 4 3 0 1
  | 4 => tabG247 1 1 0 4 3 0 2
  | 5 => tabG247 1 1 0 4 4 0 0
  | 6 => tabG247 1 1 0 4 4 0 1
  | 7 => tabG247 1 1 0 4 4 0 2
  | 8 => tabG247 1 1 1 0 3 0 0
  | 9 => tabG247 1 1 1 0 3 0 1
  | 10 => tabG247 1 1 1 0 3 0 2
  | 11 => tabG247 1 1 1 0 4 0 0
  | 12 => tabG247 1 1 1 0 4 0 1
  | 13 => tabG247 1 1 1 0 4 0 2
  | 14 => tabG247 1 1 1 1 3 0 0
  | 15 => tabG247 1 1 1 1 3 0 1
  | 16 => tabG247 1 1 1 1 3 0 2
  | 17 => tabG247 1 1 1 1 4 0 0
  | 18 => tabG247 1 1 1 1 4 0 1
  | 19 => tabG247 1 1 1 1 4 0 2
  | 20 => tabG247 1 1 1 2 3 0 0
  | 21 => tabG247 1 1 1 2 3 0 1
  | 22 => tabG247 1 1 1 2 3 0 2
  | 23 => tabG247 1 1 1 2 4 0 0
  | 24 => tabG247 1 1 1 2 4 0 1
  | 25 => tabG247 1 1 1 2 4 0 2
  | 26 => tabG247 1 1 1 3 0 0 0
  | _ => tabG247 1 1 1 3 0 0 1
def memRowG24723 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 1 3 0 0 2
  | 1 => tabG247 1 1 1 3 1 0 0
  | 2 => tabG247 1 1 1 3 1 0 1
  | 3 => tabG247 1 1 1 3 1 0 2
  | 4 => tabG247 1 1 1 3 2 0 0
  | 5 => tabG247 1 1 1 3 2 0 1
  | 6 => tabG247 1 1 1 3 2 0 2
  | 7 => tabG247 1 1 1 3 3 0 0
  | 8 => tabG247 1 1 1 3 3 0 1
  | 9 => tabG247 1 1 1 3 3 0 2
  | 10 => tabG247 1 1 1 3 4 0 0
  | 11 => tabG247 1 1 1 3 4 0 1
  | 12 => tabG247 1 1 1 3 4 0 2
  | 13 => tabG247 1 1 1 4 0 0 0
  | 14 => tabG247 1 1 1 4 0 0 1
  | 15 => tabG247 1 1 1 4 0 0 2
  | 16 => tabG247 1 1 1 4 1 0 0
  | 17 => tabG247 1 1 1 4 1 0 1
  | 18 => tabG247 1 1 1 4 1 0 2
  | 19 => tabG247 1 1 1 4 2 0 0
  | 20 => tabG247 1 1 1 4 2 0 1
  | 21 => tabG247 1 1 1 4 2 0 2
  | 22 => tabG247 1 1 1 4 3 0 0
  | 23 => tabG247 1 1 1 4 3 0 1
  | 24 => tabG247 1 1 1 4 3 0 2
  | 25 => tabG247 1 1 1 4 4 0 0
  | 26 => tabG247 1 1 1 4 4 0 1
  | _ => tabG247 1 1 1 4 4 0 2
def memRowG24724 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 2 0 3 0 0
  | 1 => tabG247 1 1 2 0 3 0 1
  | 2 => tabG247 1 1 2 0 3 0 2
  | 3 => tabG247 1 1 2 0 4 0 0
  | 4 => tabG247 1 1 2 0 4 0 1
  | 5 => tabG247 1 1 2 0 4 0 2
  | 6 => tabG247 1 1 2 1 3 0 0
  | 7 => tabG247 1 1 2 1 3 0 1
  | 8 => tabG247 1 1 2 1 3 0 2
  | 9 => tabG247 1 1 2 1 4 0 0
  | 10 => tabG247 1 1 2 1 4 0 1
  | 11 => tabG247 1 1 2 1 4 0 2
  | 12 => tabG247 1 1 2 2 3 0 0
  | 13 => tabG247 1 1 2 2 3 0 1
  | 14 => tabG247 1 1 2 2 3 0 2
  | 15 => tabG247 1 1 2 2 4 0 0
  | 16 => tabG247 1 1 2 2 4 0 1
  | 17 => tabG247 1 1 2 2 4 0 2
  | 18 => tabG247 1 1 2 3 0 0 0
  | 19 => tabG247 1 1 2 3 0 0 1
  | 20 => tabG247 1 1 2 3 0 0 2
  | 21 => tabG247 1 1 2 3 1 0 0
  | 22 => tabG247 1 1 2 3 1 0 1
  | 23 => tabG247 1 1 2 3 1 0 2
  | 24 => tabG247 1 1 2 3 2 0 0
  | 25 => tabG247 1 1 2 3 2 0 1
  | 26 => tabG247 1 1 2 3 2 0 2
  | _ => tabG247 1 1 2 3 3 0 0
def memRowG24725 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 2 3 3 0 1
  | 1 => tabG247 1 1 2 3 3 0 2
  | 2 => tabG247 1 1 2 3 4 0 0
  | 3 => tabG247 1 1 2 3 4 0 1
  | 4 => tabG247 1 1 2 3 4 0 2
  | 5 => tabG247 1 1 2 4 0 0 0
  | 6 => tabG247 1 1 2 4 0 0 1
  | 7 => tabG247 1 1 2 4 0 0 2
  | 8 => tabG247 1 1 2 4 1 0 0
  | 9 => tabG247 1 1 2 4 1 0 1
  | 10 => tabG247 1 1 2 4 1 0 2
  | 11 => tabG247 1 1 2 4 2 0 0
  | 12 => tabG247 1 1 2 4 2 0 1
  | 13 => tabG247 1 1 2 4 2 0 2
  | 14 => tabG247 1 1 2 4 3 0 0
  | 15 => tabG247 1 1 2 4 3 0 1
  | 16 => tabG247 1 1 2 4 3 0 2
  | 17 => tabG247 1 1 2 4 4 0 0
  | 18 => tabG247 1 1 2 4 4 0 1
  | 19 => tabG247 1 1 2 4 4 0 2
  | 20 => tabG247 1 1 3 0 3 0 0
  | 21 => tabG247 1 1 3 0 3 0 1
  | 22 => tabG247 1 1 3 0 3 0 2
  | 23 => tabG247 1 1 3 0 4 0 0
  | 24 => tabG247 1 1 3 0 4 0 1
  | 25 => tabG247 1 1 3 0 4 0 2
  | 26 => tabG247 1 1 3 1 3 0 0
  | _ => tabG247 1 1 3 1 3 0 1
def memRowG24726 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 3 1 3 0 2
  | 1 => tabG247 1 1 3 1 4 0 0
  | 2 => tabG247 1 1 3 1 4 0 1
  | 3 => tabG247 1 1 3 1 4 0 2
  | 4 => tabG247 1 1 3 2 3 0 0
  | 5 => tabG247 1 1 3 2 3 0 1
  | 6 => tabG247 1 1 3 2 3 0 2
  | 7 => tabG247 1 1 3 2 4 0 0
  | 8 => tabG247 1 1 3 2 4 0 1
  | 9 => tabG247 1 1 3 2 4 0 2
  | 10 => tabG247 1 1 3 3 0 0 0
  | 11 => tabG247 1 1 3 3 0 0 1
  | 12 => tabG247 1 1 3 3 0 0 2
  | 13 => tabG247 1 1 3 3 1 0 0
  | 14 => tabG247 1 1 3 3 1 0 1
  | 15 => tabG247 1 1 3 3 1 0 2
  | 16 => tabG247 1 1 3 3 2 0 0
  | 17 => tabG247 1 1 3 3 2 0 1
  | 18 => tabG247 1 1 3 3 2 0 2
  | 19 => tabG247 1 1 3 3 3 0 0
  | 20 => tabG247 1 1 3 3 3 0 1
  | 21 => tabG247 1 1 3 3 3 0 2
  | 22 => tabG247 1 1 3 3 4 0 0
  | 23 => tabG247 1 1 3 3 4 0 1
  | 24 => tabG247 1 1 3 3 4 0 2
  | 25 => tabG247 1 1 3 4 0 0 0
  | 26 => tabG247 1 1 3 4 0 0 1
  | _ => tabG247 1 1 3 4 0 0 2
def memRowG24727 : Fin 28 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabG247 1 1 3 4 1 0 0
  | 1 => tabG247 1 1 3 4 1 0 1
  | 2 => tabG247 1 1 3 4 1 0 2
  | 3 => tabG247 1 1 3 4 2 0 0
  | 4 => tabG247 1 1 3 4 2 0 1
  | 5 => tabG247 1 1 3 4 2 0 2
  | 6 => tabG247 1 1 3 4 3 0 0
  | 7 => tabG247 1 1 3 4 3 0 1
  | 8 => tabG247 1 1 3 4 3 0 2
  | 9 => tabG247 1 1 3 4 4 0 0
  | 10 => tabG247 1 1 3 4 4 0 1
  | _ => tabG247 1 1 3 4 4 0 2
def memG247 (i : Fin 768) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 28 : Nat) with
  | 0 => memRowG2470 ⟨i.1 % 28, by omega⟩
  | 1 => memRowG2471 ⟨i.1 % 28, by omega⟩
  | 2 => memRowG2472 ⟨i.1 % 28, by omega⟩
  | 3 => memRowG2473 ⟨i.1 % 28, by omega⟩
  | 4 => memRowG2474 ⟨i.1 % 28, by omega⟩
  | 5 => memRowG2475 ⟨i.1 % 28, by omega⟩
  | 6 => memRowG2476 ⟨i.1 % 28, by omega⟩
  | 7 => memRowG2477 ⟨i.1 % 28, by omega⟩
  | 8 => memRowG2478 ⟨i.1 % 28, by omega⟩
  | 9 => memRowG2479 ⟨i.1 % 28, by omega⟩
  | 10 => memRowG24710 ⟨i.1 % 28, by omega⟩
  | 11 => memRowG24711 ⟨i.1 % 28, by omega⟩
  | 12 => memRowG24712 ⟨i.1 % 28, by omega⟩
  | 13 => memRowG24713 ⟨i.1 % 28, by omega⟩
  | 14 => memRowG24714 ⟨i.1 % 28, by omega⟩
  | 15 => memRowG24715 ⟨i.1 % 28, by omega⟩
  | 16 => memRowG24716 ⟨i.1 % 28, by omega⟩
  | 17 => memRowG24717 ⟨i.1 % 28, by omega⟩
  | 18 => memRowG24718 ⟨i.1 % 28, by omega⟩
  | 19 => memRowG24719 ⟨i.1 % 28, by omega⟩
  | 20 => memRowG24720 ⟨i.1 % 28, by omega⟩
  | 21 => memRowG24721 ⟨i.1 % 28, by omega⟩
  | 22 => memRowG24722 ⟨i.1 % 28, by omega⟩
  | 23 => memRowG24723 ⟨i.1 % 28, by omega⟩
  | 24 => memRowG24724 ⟨i.1 % 28, by omega⟩
  | 25 => memRowG24725 ⟨i.1 % 28, by omega⟩
  | 26 => memRowG24726 ⟨i.1 % 28, by omega⟩
  | _ => memRowG24727 ⟨i.1 % 28, by omega⟩

/-- Which of the `768` members a given invariant tuple is, so that `mem_of_isExactG247` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrG247 : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 7, 8, 9, 10, 11, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
  30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 48, 49, 50, 51, 52, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 55, 56, 57, 58, 59, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
  81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 97,
  98, 99, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, 103, 104, 105, 106, 107, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
  126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 144, 145, 146, 147, 148, 149, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 151, 152,
  153, 154, 155, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165,
  166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
  185, 186, 187, 188, 189, 190, 191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 192, 193, 194, 195, 196, 197, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 198, 199, 200, 201, 202, 203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 204, 205, 206,
  207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225,
  226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 240, 241, 242, 243, 244, 245, 0, 0, 0, 0, 0, 0, 0, 0, 0, 246, 247, 248, 249, 250, 251, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266,
  267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
  286, 287, 0, 0, 0, 0, 0, 0, 0, 0, 0, 288, 289, 290, 291, 292, 293, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  294, 295, 296, 297, 298, 299, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300, 301, 302, 303, 304, 305, 306,
  307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325,
  326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 0, 0, 0, 0, 0, 0, 0, 0, 0, 336, 337, 338,
  339, 340, 341, 0, 0, 0, 0, 0, 0, 0, 0, 0, 342, 343, 344, 345, 346, 347, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365,
  366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 384, 385, 386, 387, 388, 389, 0, 0, 0, 0, 0, 0, 0, 0, 0, 390, 391, 392,
  393, 394, 395, 0, 0, 0, 0, 0, 0, 0, 0, 0, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
  406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424,
  425, 426, 427, 428, 429, 430, 431, 0, 0, 0, 0, 0, 0, 0, 0, 0, 432, 433, 434, 435, 436, 437, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 438, 439, 440, 441, 442, 443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 444, 445, 446,
  447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465,
  466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 480, 481, 482, 483, 484, 485, 0, 0, 0, 0, 0, 0, 0, 0, 0, 486, 487, 488, 489, 490, 491, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
  507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525,
  526, 527, 0, 0, 0, 0, 0, 0, 0, 0, 0, 528, 529, 530, 531, 532, 533, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  534, 535, 536, 537, 538, 539, 0, 0, 0, 0, 0, 0, 0, 0, 0, 540, 541, 542, 543, 544, 545, 546,
  547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565,
  566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 0, 0, 0, 0, 0, 0, 0, 0, 0, 576, 577, 578,
  579, 580, 581, 0, 0, 0, 0, 0, 0, 0, 0, 0, 582, 583, 584, 585, 586, 587, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605,
  606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 624, 625, 626, 627, 628, 629, 0, 0, 0, 0, 0, 0, 0, 0, 0, 630, 631, 632,
  633, 634, 635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645,
  646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664,
  665, 666, 667, 668, 669, 670, 671, 0, 0, 0, 0, 0, 0, 0, 0, 0, 672, 673, 674, 675, 676, 677, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 678, 679, 680, 681, 682, 683, 0, 0, 0, 0, 0, 0, 0, 0, 0, 684, 685, 686,
  687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705,
  706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 720, 721, 722, 723, 724, 725, 0, 0, 0, 0, 0, 0, 0, 0, 0, 726, 727, 728, 729, 730, 731, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746,
  747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765,
  766, 767]

/-- The arguments as one mixed-radix index, which is how `rankArrG247` is addressed. -/
def encTG247 (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Nat :=
  a.1 * 600 +
    b.1 * 300 +
    c.1 * 75 +
    d.1 * 15 +
    e.1 * 3 +
    f.1 * 3 +
    g.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankG247 (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3) : Fin 768 :=
  ⟨min (rankArrG247.getD (encTG247 a b c d e f g) 0) 767, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactG247 (i : Fin 768) : Magma (Fin 7) := Magma.mk (memG247 i)

theorem exactG247_isEndo (i : Fin 768) (j : Fin 24) : (exactG247 i).IsEndo ⇑(eEG247 j) := by
  simp only [eEG247, coe_permOf]; revert i j; native_decide

theorem exactG247_not_isEndo (i : Fin 768) (j : Fin 1) : ¬ (exactG247 i).IsEndo ⇑(eXG247 j) := by
  simp only [eXG247, coe_permOf]; revert i j; native_decide

/-- `rankG247` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memG247` for the index would be a comparison per tuple and
member. -/
theorem mem_rankG247 (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3)
    (h : Magma.isExact (tabG247 a b c d e f g) permEG247 permXG247 = true) :
    memG247 (rankG247 a b c d e f g) = tabG247 a b c d e f g := by
  revert h; revert a b c d e f g; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `768`
listed members. -/
theorem mem_of_isExactG247 (a b : Fin 2) (c : Fin 4) (d e : Fin 5) (f : Fin 1) (g : Fin 3)
    (h : Magma.isExact (tabG247 a b c d e f g) permEG247 permXG247 = true) :
    ∃ i, memG247 i = tabG247 a b c d e f g :=
  ⟨_, mem_rankG247 a b c d e f g h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactG247`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactG247` turns that into a member index. -/
theorem exists_exactG247 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eEG247 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXG247 i)) : ∃ i, exactG247 i = M := by
  simp only [eEG247, coe_permOf] at hE
  simp only [eXG247, coe_permOf] at hX
  have hop : M.op = Magma.transport permEG247 trG247 (fun i ↦ M.op (repG247 i).1 (repG247 i).2) :=
    Magma.op_eq_transport (rep := repG247) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2470) (a := (repG247 0).1) (b := (repG247 0).2)
    (val := valG2470) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2471) (a := (repG247 1).1) (b := (repG247 1).2)
    (val := valG2471) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2472) (a := (repG247 2).1) (b := (repG247 2).2)
    (val := valG2472) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2473) (a := (repG247 3).1) (b := (repG247 3).2)
    (val := valG2473) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2474) (a := (repG247 4).1) (b := (repG247 4).2)
    (val := valG2474) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2475) (a := (repG247 5).1) (b := (repG247 5).2)
    (val := valG2475) hE (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permEG247) (idx := stabIdxG2476) (a := (repG247 6).1) (b := (repG247 6).2)
    (val := valG2476) hE (by decide) (by decide)
  have hdec : decG247 a b c d e f g = fun i ↦ M.op (repG247 i).1 (repG247 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
  have key : tabG247 a b c d e f g = M.op := by
    rw [tabG247_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabG247 a b c d e f g) permEG247 permXG247 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactG247 a b c d e f g hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`24` group of `Magma.permEG247`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactG247 {L L' : Law.NatMagmaLaw} {i : Fin 768}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactG247 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactG247 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactG247 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactG247
    (fun k ↦ (Magma.exactG247_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactG247_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
