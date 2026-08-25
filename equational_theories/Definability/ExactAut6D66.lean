import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D66` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`12` group `⟨(0 1)(2 3)(4 5), (0 1 2 4 5 3)⟩` -/

/-- The `12` elements of the group: `()`, `(1 3)(2 5)`, `(0 1)(2 3)(4 5)`, `(0 1 2 4 5 3)`, `(0 2)(3
4)`, `(0 2 5)(1 4 3)`, `(0 3 5 4 2 1)`, `(0 3)(1 5)(2 4)`, `(0 4)(1 2)(3 5)`, `(0 4)(1 5)(2 3)`, `(0
5 2)(1 3 4)`, `(0 5)(1 4)`. -/
def pED660 : Fin 6 → Fin 6 := id
def pED661 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 2
def pED662 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pED663 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 3
def pED664 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5
def pED665 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 0
def pED666 : Fin 6 → Fin 6 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 4
def pED667 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 1
def pED668 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 0 | 5 => 3
def pED669 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 1
def pED6610 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 2
def pED6611 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 0

def permED66 : Fin 12 → Fin 6 → Fin 6
  | 0 => pED660
  | 1 => pED661
  | 2 => pED662
  | 3 => pED663
  | 4 => pED664
  | 5 => pED665
  | 6 => pED666
  | 7 => pED667
  | 8 => pED668
  | 9 => pED669
  | 10 => pED6610
  | 11 => pED6611

def permEinvD66 : Fin 12 → Fin 6 → Fin 6
  | 0 => pED660
  | 1 => pED661
  | 2 => pED662
  | 3 => pED666
  | 4 => pED664
  | 5 => pED6610
  | 6 => pED663
  | 7 => pED667
  | 8 => pED668
  | 9 => pED669
  | 10 => pED665
  | 11 => pED6611

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED66 (i : Fin 12) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permED66 i) (permEinvD66 i) (by revert i; decide)

/-- The `3` permutations that must *not* be automorphisms: `(1 2 5 3 4)`, `(0 1 2)(3 4 5)`, `(0 1 2
3 5 4)`. Every subgroup properly containing the group above contains one of them, so a magma
admitting the group and not these has that group as its automorphism group exactly. -/
def pXD660 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 3
def pXD661 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pXD662 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 5 | 4 => 0 | 5 => 4
def pXD660inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 2
def pXD661inv : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pXD662inv : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 3

def permXD66 : Fin 3 → Fin 6 → Fin 6
  | 0 => pXD660
  | 1 => pXD661
  | 2 => pXD662

def permXinvD66 : Fin 3 → Fin 6 → Fin 6
  | 0 => pXD660inv
  | 1 => pXD661inv
  | 2 => pXD662inv

def eXD66 (i : Fin 3) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXD66 i) (permXinvD66 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def repD66 : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD66 : Fin 6 → Fin 6 → Fin 4 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (1, 1)
  | 0, 4 => (3, 0)
  | 0, 5 => (2, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 3)
  | 1, 3 => (2, 2)
  | 1, 4 => (2, 3)
  | 1, 5 => (3, 2)
  | 2, 0 => (2, 4)
  | 2, 1 => (1, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 4)
  | 2, 4 => (1, 5)
  | 2, 5 => (2, 5)
  | 3, 0 => (1, 6)
  | 3, 1 => (2, 6)
  | 3, 2 => (3, 6)
  | 3, 3 => (0, 6)
  | 3, 4 => (2, 7)
  | 3, 5 => (1, 7)
  | 4, 0 => (3, 8)
  | 4, 1 => (2, 8)
  | 4, 2 => (1, 8)
  | 4, 3 => (2, 9)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 9)
  | 5, 0 => (2, 10)
  | 5, 1 => (3, 10)
  | 5, 2 => (2, 11)
  | 5, 3 => (1, 10)
  | 5, 4 => (1, 11)
  | 5, 5 => (0, 10)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD660 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def valD660 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 4

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxD661 : Fin 1 → Fin 12
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxD662 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD663 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def valD663 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 4

/-- The `4` orbit values named by the family's arguments. -/
def decD66 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 4 → Fin 6
  | 0 => valD660 a
  | 1 => b
  | 2 => c
  | 3 => valD663 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD66_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD66 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valD660 a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => pED661 b
  | 0, 4 => valD663 d
  | 0, 5 => pED661 c
  | 1, 0 => pED662 b
  | 1, 1 => pED662 (valD660 a)
  | 1, 2 => pED663 b
  | 1, 3 => pED662 c
  | 1, 4 => pED663 c
  | 1, 5 => pED662 (valD663 d)
  | 2, 0 => pED664 c
  | 2, 1 => pED664 b
  | 2, 2 => pED664 (valD660 a)
  | 2, 3 => pED664 (valD663 d)
  | 2, 4 => pED665 b
  | 2, 5 => pED665 c
  | 3, 0 => pED666 b
  | 3, 1 => pED666 c
  | 3, 2 => pED666 (valD663 d)
  | 3, 3 => pED666 (valD660 a)
  | 3, 4 => pED667 c
  | 3, 5 => pED667 b
  | 4, 0 => pED668 (valD663 d)
  | 4, 1 => pED668 c
  | 4, 2 => pED668 b
  | 4, 3 => pED669 c
  | 4, 4 => pED668 (valD660 a)
  | 4, 5 => pED669 b
  | 5, 0 => pED6610 c
  | 5, 1 => pED6610 (valD663 d)
  | 5, 2 => pED6611 c
  | 5, 3 => pED6610 b
  | 5, 4 => pED6611 b
  | 5, 5 => pED6610 (valD660 a)

theorem tabD66_eq_transport (a : Fin 2) (b c : Fin 6) (d : Fin 2) :
    tabD66 a b c d = Magma.transport permED66 trD66 (decD66 a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `124` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `144` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowD660 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 0 0 1 0
  | 1 => tabD66 0 0 1 1
  | 2 => tabD66 0 0 2 1
  | 3 => tabD66 0 0 3 0
  | 4 => tabD66 0 0 3 1
  | 5 => tabD66 0 0 4 0
  | 6 => tabD66 0 0 4 1
  | 7 => tabD66 0 0 5 1
  | 8 => tabD66 0 1 0 0
  | 9 => tabD66 0 1 1 0
  | 10 => tabD66 0 1 1 1
  | _ => tabD66 0 1 3 0
def memRowD661 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 0 1 3 1
  | 1 => tabD66 0 1 4 0
  | 2 => tabD66 0 1 4 1
  | 3 => tabD66 0 1 5 0
  | 4 => tabD66 0 2 0 0
  | 5 => tabD66 0 2 0 1
  | 6 => tabD66 0 2 1 0
  | 7 => tabD66 0 2 1 1
  | 8 => tabD66 0 2 2 0
  | 9 => tabD66 0 2 2 1
  | 10 => tabD66 0 2 3 0
  | _ => tabD66 0 2 3 1
def memRowD662 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 0 2 4 0
  | 1 => tabD66 0 2 4 1
  | 2 => tabD66 0 2 5 0
  | 3 => tabD66 0 2 5 1
  | 4 => tabD66 0 3 0 0
  | 5 => tabD66 0 3 0 1
  | 6 => tabD66 0 3 1 0
  | 7 => tabD66 0 3 1 1
  | 8 => tabD66 0 3 2 0
  | 9 => tabD66 0 3 2 1
  | 10 => tabD66 0 3 3 0
  | _ => tabD66 0 3 3 1
def memRowD663 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 0 3 4 0
  | 1 => tabD66 0 3 4 1
  | 2 => tabD66 0 3 5 0
  | 3 => tabD66 0 3 5 1
  | 4 => tabD66 0 4 0 0
  | 5 => tabD66 0 4 0 1
  | 6 => tabD66 0 4 1 0
  | 7 => tabD66 0 4 1 1
  | 8 => tabD66 0 4 2 0
  | 9 => tabD66 0 4 2 1
  | 10 => tabD66 0 4 3 0
  | _ => tabD66 0 4 3 1
def memRowD664 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 0 4 5 0
  | 1 => tabD66 0 4 5 1
  | 2 => tabD66 0 5 0 0
  | 3 => tabD66 0 5 0 1
  | 4 => tabD66 0 5 1 0
  | 5 => tabD66 0 5 1 1
  | 6 => tabD66 0 5 2 0
  | 7 => tabD66 0 5 2 1
  | 8 => tabD66 0 5 4 0
  | 9 => tabD66 0 5 4 1
  | 10 => tabD66 0 5 5 0
  | _ => tabD66 0 5 5 1
def memRowD665 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 1 0 1 0
  | 1 => tabD66 1 0 1 1
  | 2 => tabD66 1 0 2 0
  | 3 => tabD66 1 0 2 1
  | 4 => tabD66 1 0 3 0
  | 5 => tabD66 1 0 3 1
  | 6 => tabD66 1 0 4 0
  | 7 => tabD66 1 0 4 1
  | 8 => tabD66 1 0 5 0
  | 9 => tabD66 1 0 5 1
  | 10 => tabD66 1 1 0 0
  | _ => tabD66 1 1 0 1
def memRowD666 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 1 1 1 0
  | 1 => tabD66 1 1 1 1
  | 2 => tabD66 1 1 3 0
  | 3 => tabD66 1 1 3 1
  | 4 => tabD66 1 1 4 0
  | 5 => tabD66 1 1 4 1
  | 6 => tabD66 1 1 5 0
  | 7 => tabD66 1 1 5 1
  | 8 => tabD66 1 2 0 0
  | 9 => tabD66 1 2 0 1
  | 10 => tabD66 1 2 1 0
  | _ => tabD66 1 2 1 1
def memRowD667 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 1 2 2 0
  | 1 => tabD66 1 2 2 1
  | 2 => tabD66 1 2 3 0
  | 3 => tabD66 1 2 3 1
  | 4 => tabD66 1 2 4 0
  | 5 => tabD66 1 2 4 1
  | 6 => tabD66 1 2 5 0
  | 7 => tabD66 1 2 5 1
  | 8 => tabD66 1 3 0 0
  | 9 => tabD66 1 3 0 1
  | 10 => tabD66 1 3 1 0
  | _ => tabD66 1 3 1 1
def memRowD668 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 1 3 2 0
  | 1 => tabD66 1 3 2 1
  | 2 => tabD66 1 3 3 0
  | 3 => tabD66 1 3 3 1
  | 4 => tabD66 1 3 4 0
  | 5 => tabD66 1 3 4 1
  | 6 => tabD66 1 3 5 0
  | 7 => tabD66 1 3 5 1
  | 8 => tabD66 1 4 0 0
  | 9 => tabD66 1 4 0 1
  | 10 => tabD66 1 4 1 0
  | _ => tabD66 1 4 1 1
def memRowD669 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 1 4 2 0
  | 1 => tabD66 1 4 2 1
  | 2 => tabD66 1 4 3 0
  | 3 => tabD66 1 4 3 1
  | 4 => tabD66 1 4 5 0
  | 5 => tabD66 1 4 5 1
  | 6 => tabD66 1 5 0 0
  | 7 => tabD66 1 5 0 1
  | 8 => tabD66 1 5 1 0
  | 9 => tabD66 1 5 1 1
  | 10 => tabD66 1 5 2 0
  | _ => tabD66 1 5 2 1
def memRowD6610 : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabD66 1 5 4 0
  | 1 => tabD66 1 5 4 1
  | 2 => tabD66 1 5 5 0
  | _ => tabD66 1 5 5 1
def memD66 (i : Fin 124) : Fin 6 → Fin 6 → Fin 6 :=
  match (i.1 / 12 : Nat) with
  | 0 => memRowD660 ⟨i.1 % 12, by omega⟩
  | 1 => memRowD661 ⟨i.1 % 12, by omega⟩
  | 2 => memRowD662 ⟨i.1 % 12, by omega⟩
  | 3 => memRowD663 ⟨i.1 % 12, by omega⟩
  | 4 => memRowD664 ⟨i.1 % 12, by omega⟩
  | 5 => memRowD665 ⟨i.1 % 12, by omega⟩
  | 6 => memRowD666 ⟨i.1 % 12, by omega⟩
  | 7 => memRowD667 ⟨i.1 % 12, by omega⟩
  | 8 => memRowD668 ⟨i.1 % 12, by omega⟩
  | 9 => memRowD669 ⟨i.1 % 12, by omega⟩
  | _ => memRowD6610 ⟨i.1 % 12, by omega⟩

/-- Which of the `124` members a given invariant tuple is, so that `mem_of_isExactD66` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD66 : Array Nat := #[
  0, 0, 0, 1, 0, 2, 3, 4, 5, 6, 0, 7, 8, 0, 9, 10, 0, 0, 11, 12, 13, 14, 15, 0, 16, 17, 18, 19,
  20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44, 45, 46, 47, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 56, 57, 58, 59, 0, 0, 60, 61, 62,
  63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 0, 0, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
  85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
  107, 108, 109, 110, 111, 0, 0, 112, 113, 114, 115, 116, 117, 118, 119, 0, 0, 120, 121, 122, 123]

/-- The arguments as one mixed-radix index, which is how `rankArrD66` is addressed. -/
def encTD66 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Nat :=
  a.1 * 72 +
    b.1 * 12 +
    c.1 * 2 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD66 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 124 :=
  ⟨min (rankArrD66.getD (encTD66 a b c d) 0) 123, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD66 (i : Fin 124) : Magma (Fin 6) := Magma.mk (memD66 i)

theorem exactD66_isEndo (i : Fin 124) (j : Fin 12) : (exactD66 i).IsEndo ⇑(eED66 j) := by
  simp only [eED66, coe_permOf]; revert i j; native_decide

theorem exactD66_not_isEndo (i : Fin 124) (j : Fin 3) : ¬ (exactD66 i).IsEndo ⇑(eXD66 j) := by
  simp only [eXD66, coe_permOf]; revert i j; native_decide

/-- `rankD66` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD66` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD66 (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tabD66 a b c d) permED66 permXD66 = true) :
    memD66 (rankD66 a b c d) = tabD66 a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `124`
listed members. -/
theorem mem_of_isExactD66 (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tabD66 a b c d) permED66 permXD66 = true) :
    ∃ i, memD66 i = tabD66 a b c d :=
  ⟨_, mem_rankD66 a b c d h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD66`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD66` turns that into a member index. -/
theorem exists_exactD66 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eED66 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD66 i)) : ∃ i, exactD66 i = M := by
  simp only [eED66, coe_permOf] at hE
  simp only [eXD66, coe_permOf] at hX
  have hop : M.op = Magma.transport permED66 trD66 (fun i ↦ M.op (repD66 i).1 (repD66 i).2) :=
    Magma.op_eq_transport (rep := repD66) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED66) (idx := stabIdxD660) (a := (repD66 0).1) (b := (repD66 0).2)
    (val := valD660) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED66) (idx := stabIdxD661) (a := (repD66 1).1) (b := (repD66 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED66) (idx := stabIdxD662) (a := (repD66 2).1) (b := (repD66 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permED66) (idx := stabIdxD663) (a := (repD66 3).1) (b := (repD66 3).2)
    (val := valD663) hE (by decide) (by decide)
  have hdec : decD66 a b c d = fun i ↦ M.op (repD66 i).1 (repD66 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tabD66 a b c d = M.op := by
    rw [tabD66_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD66 a b c d) permED66 permXD66 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD66 a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`12` group of `Magma.permED66`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD66 {L L' : Law.NatMagmaLaw} {i : Fin 124}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactD66 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactD66 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD66 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD66
    (fun k ↦ (Magma.exactD66_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD66_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
