import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `F427` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`42` group `⟨(0 1 5 3 4 6 2), (1 2)(3 4)(5 6), (1 3 5 2 4 6)⟩` -/

/-- The `42` elements of the group: `()`, `(1 2)(3 4)(5 6)`, `(1 3 5 2 4 6)`, `(1 4 5)(2 3 6)`, `(1
5 4)(2 6 3)`, `(1 6 4 2 5 3)`, `(0 1)(2 5)(3 6)`, `(0 1 2 3 5 4)`, `(0 1 3)(4 5 6)`, `(0 1 4 2 6
5)`, `(0 1 5 3 4 6 2)`, `(0 1 6)(2 4 3)`, `(0 2 6 4 3 5 1)`, `(0 2 4)(3 6 5)`, `(0 2 5)(1 3 4)`, `(0
2 1 4 6 3)`, `(0 2 3 1 5 6)`, `(0 2)(1 6)(4 5)`, `(0 3 1)(4 6 5)`, `(0 3 4 5 2 6)`, `(0 3 6 4 1 2)`,
`(0 3 2 5 6 1 4)`, `(0 3)(1 5)(2 4)`, `(0 3 5)(1 6 2)`, `(0 4 5 3 2 1)`, `(0 4 2)(3 5 6)`, `(0 4
6)(1 2 5)`, `(0 4)(1 3)(2 6)`, `(0 4 3 6 1 5)`, `(0 4 1 6 5 2 3)`, `(0 5 6 2 4 1)`, `(0 5)(2 3)(4
6)`, `(0 5 3)(1 2 6)`, `(0 5 4 2 1 3 6)`, `(0 5 2)(1 4 3)`, `(0 5 1 6 3 4)`, `(0 6 1)(2 3 4)`, `(0 6
2 5 4 3)`, `(0 6 3 1 2 4 5)`, `(0 6 5 1 3 2)`, `(0 6)(1 4)(3 5)`, `(0 6 4)(1 5 2)`. -/
def pEF4270 : Fin 7 → Fin 7 := id
def pEF4271 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pEF4272 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 2 | 6 => 1
def pEF4273 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 6 | 4 => 5 | 5 => 1 | 6 => 2
def pEF4274 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 6 | 3 => 2 | 4 => 1 | 5 => 4 | 6 => 3
def pEF4275 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 5 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4
def pEF4276 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 6 | 4 => 4 | 5 => 2 | 6 => 3
def pEF4277 : Fin 7 → Fin 7 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 5 | 4 => 0 | 5 => 4 | 6 => 6
def pEF4278 : Fin 7 → Fin 7 | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 6 | 6 => 4
def pEF4279 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 6 | 3 => 3 | 4 => 2 | 5 => 0 | 6 => 5
def pEF42710 : Fin 7 → Fin 7 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 6 | 5 => 3 | 6 => 2
def pEF42711 : Fin 7 → Fin 7 | 0 => 1 | 1 => 6 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 0
def pEF42712 : Fin 7 → Fin 7 | 0 => 2 | 1 => 0 | 2 => 6 | 3 => 5 | 4 => 3 | 5 => 1 | 6 => 4
def pEF42713 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 6 | 4 => 0 | 5 => 3 | 6 => 5
def pEF42714 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 0 | 6 => 6
def pEF42715 : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 3
def pEF42716 : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 0
def pEF42717 : Fin 7 → Fin 7 | 0 => 2 | 1 => 6 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 1
def pEF42718 : Fin 7 → Fin 7 | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 5
def pEF42719 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 6 | 3 => 4 | 4 => 5 | 5 => 2 | 6 => 0
def pEF42720 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 6 | 4 => 1 | 5 => 5 | 6 => 4
def pEF42721 : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 1
def pEF42722 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 1 | 6 => 6
def pEF42723 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 0 | 6 => 2
def pEF42724 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 3 | 6 => 6
def pEF42725 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 2 | 5 => 6 | 6 => 3
def pEF42726 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 6 | 5 => 1 | 6 => 0
def pEF42727 : Fin 7 → Fin 7 | 0 => 4 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 2
def pEF42728 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 2 | 3 => 6 | 4 => 3 | 5 => 0 | 6 => 1
def pEF42729 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 5
def pEF42730 : Fin 7 → Fin 7 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 2
def pEF42731 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 0 | 6 => 4
def pEF42732 : Fin 7 → Fin 7 | 0 => 5 | 1 => 2 | 2 => 6 | 3 => 0 | 4 => 4 | 5 => 3 | 6 => 1
def pEF42733 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 6 | 4 => 2 | 5 => 4 | 6 => 0
def pEF42734 : Fin 7 → Fin 7 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 6
def pEF42735 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 1 | 6 => 3
def pEF42736 : Fin 7 → Fin 7 | 0 => 6 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 1
def pEF42737 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 5 | 3 => 0 | 4 => 3 | 5 => 4 | 6 => 2
def pEF42738 : Fin 7 → Fin 7 | 0 => 6 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 5 | 5 => 0 | 6 => 3
def pEF42739 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 1 | 6 => 5
def pEF42740 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 0
def pEF42741 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 2 | 6 => 4

def permEF427 : Fin 42 → Fin 7 → Fin 7
  | 0 => pEF4270
  | 1 => pEF4271
  | 2 => pEF4272
  | 3 => pEF4273
  | 4 => pEF4274
  | 5 => pEF4275
  | 6 => pEF4276
  | 7 => pEF4277
  | 8 => pEF4278
  | 9 => pEF4279
  | 10 => pEF42710
  | 11 => pEF42711
  | 12 => pEF42712
  | 13 => pEF42713
  | 14 => pEF42714
  | 15 => pEF42715
  | 16 => pEF42716
  | 17 => pEF42717
  | 18 => pEF42718
  | 19 => pEF42719
  | 20 => pEF42720
  | 21 => pEF42721
  | 22 => pEF42722
  | 23 => pEF42723
  | 24 => pEF42724
  | 25 => pEF42725
  | 26 => pEF42726
  | 27 => pEF42727
  | 28 => pEF42728
  | 29 => pEF42729
  | 30 => pEF42730
  | 31 => pEF42731
  | 32 => pEF42732
  | 33 => pEF42733
  | 34 => pEF42734
  | 35 => pEF42735
  | 36 => pEF42736
  | 37 => pEF42737
  | 38 => pEF42738
  | 39 => pEF42739
  | 40 => pEF42740
  | _ => pEF42741

def permEinvF427 : Fin 42 → Fin 7 → Fin 7
  | 0 => pEF4270
  | 1 => pEF4271
  | 2 => pEF4275
  | 3 => pEF4274
  | 4 => pEF4273
  | 5 => pEF4272
  | 6 => pEF4276
  | 7 => pEF42724
  | 8 => pEF42718
  | 9 => pEF42730
  | 10 => pEF42712
  | 11 => pEF42736
  | 12 => pEF42710
  | 13 => pEF42725
  | 14 => pEF42734
  | 15 => pEF42720
  | 16 => pEF42739
  | 17 => pEF42717
  | 18 => pEF4278
  | 19 => pEF42737
  | 20 => pEF42715
  | 21 => pEF42729
  | 22 => pEF42722
  | 23 => pEF42732
  | 24 => pEF4277
  | 25 => pEF42713
  | 26 => pEF42741
  | 27 => pEF42727
  | 28 => pEF42735
  | 29 => pEF42721
  | 30 => pEF4279
  | 31 => pEF42731
  | 32 => pEF42723
  | 33 => pEF42738
  | 34 => pEF42714
  | 35 => pEF42728
  | 36 => pEF42711
  | 37 => pEF42719
  | 38 => pEF42733
  | 39 => pEF42716
  | 40 => pEF42740
  | _ => pEF42726

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEF427 (i : Fin 42) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permEF427 i) (permEinvF427 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 4 5 3 6 2)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXF4270 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 6 | 4 => 5 | 5 => 3 | 6 => 2
def pXF4270inv : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 6 | 3 => 5 | 4 => 0 | 5 => 4 | 6 => 3

def permXF427 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXF4270

def permXinvF427 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXF4270inv

def eXF427 (i : Fin 1) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXF427 i) (permXinvF427 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `2`, so an invariant
operation is `2` values. -/
def repF427 : Fin 2 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trF427 : Fin 7 → Fin 7 → Fin 2 × Fin 42
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 0, 4 => (1, 3)
  | 0, 5 => (1, 4)
  | 0, 6 => (1, 5)
  | 1, 0 => (1, 6)
  | 1, 1 => (0, 6)
  | 1, 2 => (1, 7)
  | 1, 3 => (1, 8)
  | 1, 4 => (1, 9)
  | 1, 5 => (1, 10)
  | 1, 6 => (1, 11)
  | 2, 0 => (1, 12)
  | 2, 1 => (1, 13)
  | 2, 2 => (0, 12)
  | 2, 3 => (1, 14)
  | 2, 4 => (1, 15)
  | 2, 5 => (1, 16)
  | 2, 6 => (1, 17)
  | 3, 0 => (1, 18)
  | 3, 1 => (1, 19)
  | 3, 2 => (1, 20)
  | 3, 3 => (0, 18)
  | 3, 4 => (1, 21)
  | 3, 5 => (1, 22)
  | 3, 6 => (1, 23)
  | 4, 0 => (1, 24)
  | 4, 1 => (1, 25)
  | 4, 2 => (1, 26)
  | 4, 3 => (1, 27)
  | 4, 4 => (0, 24)
  | 4, 5 => (1, 28)
  | 4, 6 => (1, 29)
  | 5, 0 => (1, 30)
  | 5, 1 => (1, 31)
  | 5, 2 => (1, 32)
  | 5, 3 => (1, 33)
  | 5, 4 => (1, 34)
  | 5, 5 => (0, 30)
  | 5, 6 => (1, 35)
  | 6, 0 => (1, 36)
  | 6, 1 => (1, 37)
  | 6, 2 => (1, 38)
  | 6, 3 => (1, 39)
  | 6, 4 => (1, 40)
  | 6, 5 => (1, 41)
  | 6, 6 => (0, 36)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxF4270 : Fin 6 → Fin 42
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valF4270 : Fin 1 → Fin 7
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxF4271 : Fin 1 → Fin 42
  | 0 => 0

/-- The `2` orbit values named by the family's arguments. -/
def decF427 (a : Fin 1) (b : Fin 7) : Fin 2 → Fin 7
  | 0 => valF4270 a
  | 1 => b

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabF427_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabF427 (a : Fin 1) (b : Fin 7) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valF4270 a
  | 0, 1 => b
  | 0, 2 => pEF4271 b
  | 0, 3 => pEF4272 b
  | 0, 4 => pEF4273 b
  | 0, 5 => pEF4274 b
  | 0, 6 => pEF4275 b
  | 1, 0 => pEF4276 b
  | 1, 1 => pEF4276 (valF4270 a)
  | 1, 2 => pEF4277 b
  | 1, 3 => pEF4278 b
  | 1, 4 => pEF4279 b
  | 1, 5 => pEF42710 b
  | 1, 6 => pEF42711 b
  | 2, 0 => pEF42712 b
  | 2, 1 => pEF42713 b
  | 2, 2 => pEF42712 (valF4270 a)
  | 2, 3 => pEF42714 b
  | 2, 4 => pEF42715 b
  | 2, 5 => pEF42716 b
  | 2, 6 => pEF42717 b
  | 3, 0 => pEF42718 b
  | 3, 1 => pEF42719 b
  | 3, 2 => pEF42720 b
  | 3, 3 => pEF42718 (valF4270 a)
  | 3, 4 => pEF42721 b
  | 3, 5 => pEF42722 b
  | 3, 6 => pEF42723 b
  | 4, 0 => pEF42724 b
  | 4, 1 => pEF42725 b
  | 4, 2 => pEF42726 b
  | 4, 3 => pEF42727 b
  | 4, 4 => pEF42724 (valF4270 a)
  | 4, 5 => pEF42728 b
  | 4, 6 => pEF42729 b
  | 5, 0 => pEF42730 b
  | 5, 1 => pEF42731 b
  | 5, 2 => pEF42732 b
  | 5, 3 => pEF42733 b
  | 5, 4 => pEF42734 b
  | 5, 5 => pEF42730 (valF4270 a)
  | 5, 6 => pEF42735 b
  | 6, 0 => pEF42736 b
  | 6, 1 => pEF42737 b
  | 6, 2 => pEF42738 b
  | 6, 3 => pEF42739 b
  | 6, 4 => pEF42740 b
  | 6, 5 => pEF42741 b
  | 6, 6 => pEF42736 (valF4270 a)

theorem tabF427_eq_transport (a : Fin 1) (b : Fin 7) :
    tabF427 a b = Magma.transport permEF427 trF427 (decF427 a b) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `5` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `7` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memF427 : Fin 5 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF427 0 2
  | 1 => tabF427 0 3
  | 2 => tabF427 0 4
  | 3 => tabF427 0 5
  | 4 => tabF427 0 6

/-- Which of the `5` members a given invariant tuple is, so that `mem_of_isExactF427` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrF427 : Array Nat := #[
  0, 0, 0, 1, 2, 3, 4]

/-- The arguments as one mixed-radix index, which is how `rankArrF427` is addressed. -/
def encTF427 (a : Fin 1) (b : Fin 7) : Nat :=
  a.1 * 7 +
    b.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankF427 (a : Fin 1) (b : Fin 7) : Fin 5 :=
  ⟨min (rankArrF427.getD (encTF427 a b) 0) 4, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactF427 (i : Fin 5) : Magma (Fin 7) := Magma.mk (memF427 i)

theorem exactF427_isEndo (i : Fin 5) (j : Fin 42) : (exactF427 i).IsEndo ⇑(eEF427 j) := by
  simp only [eEF427, coe_permOf]; revert i j; native_decide

theorem exactF427_not_isEndo (i : Fin 5) (j : Fin 1) : ¬ (exactF427 i).IsEndo ⇑(eXF427 j) := by
  simp only [eXF427, coe_permOf]; revert i j; native_decide

/-- `rankF427` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memF427` for the index would be a comparison per tuple and
member. -/
theorem mem_rankF427 (a : Fin 1) (b : Fin 7)
    (h : Magma.isExact (tabF427 a b) permEF427 permXF427 = true) :
    memF427 (rankF427 a b) = tabF427 a b := by
  revert h; revert a b; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `5` listed
members. -/
theorem mem_of_isExactF427 (a : Fin 1) (b : Fin 7)
    (h : Magma.isExact (tabF427 a b) permEF427 permXF427 = true) :
    ∃ i, memF427 i = tabF427 a b :=
  ⟨_, mem_rankF427 a b h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactF427`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactF427` turns that into a member index. -/
theorem exists_exactF427 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eEF427 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXF427 i)) : ∃ i, exactF427 i = M := by
  simp only [eEF427, coe_permOf] at hE
  simp only [eXF427, coe_permOf] at hX
  have hop : M.op = Magma.transport permEF427 trF427 (fun i ↦ M.op (repF427 i).1 (repF427 i).2) :=
    Magma.op_eq_transport (rep := repF427) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEF427) (idx := stabIdxF4270) (a := (repF427 0).1) (b := (repF427 0).2)
    (val := valF4270) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEF427) (idx := stabIdxF4271) (a := (repF427 1).1) (b := (repF427 1).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decF427 a b = fun i ↦ M.op (repF427 i).1 (repF427 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
  have key : tabF427 a b = M.op := by
    rw [tabF427_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabF427 a b) permEF427 permXF427 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactF427 a b hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`42` group of `Magma.permEF427`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactF427 {L L' : Law.NatMagmaLaw} {i : Fin 5}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactF427 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactF427 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactF427 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactF427
    (fun k ↦ (Magma.exactF427_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactF427_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
