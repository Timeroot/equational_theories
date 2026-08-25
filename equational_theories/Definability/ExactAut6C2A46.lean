import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `C2A46` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 1 2)(3 4 5), (0 1 2 3 4 5)⟩` -/

/-- The `24` elements of the group: `()`, `(2 5)`, `(1 4)`, `(1 4)(2 5)`, `(0 1 2)(3 4 5)`, `(0 1 2
3 4 5)`, `(0 1 5 3 4 2)`, `(0 1 5)(2 3 4)`, `(0 2 1)(3 5 4)`, `(0 2 4 3 5 1)`, `(0 2 1 3 5 4)`, `(0
2 4)(1 3 5)`, `(0 3)`, `(0 3)(2 5)`, `(0 3)(1 4)`, `(0 3)(1 4)(2 5)`, `(0 4 5 3 1 2)`, `(0 4 5)(1 2
3)`, `(0 4 2)(1 5 3)`, `(0 4 2 3 1 5)`, `(0 5 4 3 2 1)`, `(0 5 1)(2 4 3)`, `(0 5 4)(1 3 2)`, `(0 5 1
3 2 4)`. -/
def pEC2A460 : Fin 6 → Fin 6 := id
def pEC2A461 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 2
def pEC2A462 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5
def pEC2A463 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 2
def pEC2A464 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pEC2A465 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 0
def pEC2A466 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 2 | 5 => 3
def pEC2A467 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 0
def pEC2A468 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pEC2A469 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 1
def pEC2A4610 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 5 | 4 => 0 | 5 => 4
def pEC2A4611 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 1
def pEC2A4612 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5
def pEC2A4613 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 2
def pEC2A4614 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5
def pEC2A4615 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 1 | 5 => 2
def pEC2A4616 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 3
def pEC2A4617 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0
def pEC2A4618 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3
def pEC2A4619 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 0
def pEC2A4620 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4
def pEC2A4621 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1
def pEC2A4622 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4
def pEC2A4623 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 1

def permEC2A46 : Fin 24 → Fin 6 → Fin 6
  | 0 => pEC2A460
  | 1 => pEC2A461
  | 2 => pEC2A462
  | 3 => pEC2A463
  | 4 => pEC2A464
  | 5 => pEC2A465
  | 6 => pEC2A466
  | 7 => pEC2A467
  | 8 => pEC2A468
  | 9 => pEC2A469
  | 10 => pEC2A4610
  | 11 => pEC2A4611
  | 12 => pEC2A4612
  | 13 => pEC2A4613
  | 14 => pEC2A4614
  | 15 => pEC2A4615
  | 16 => pEC2A4616
  | 17 => pEC2A4617
  | 18 => pEC2A4618
  | 19 => pEC2A4619
  | 20 => pEC2A4620
  | 21 => pEC2A4621
  | 22 => pEC2A4622
  | _ => pEC2A4623

def permEinvC2A46 : Fin 24 → Fin 6 → Fin 6
  | 0 => pEC2A460
  | 1 => pEC2A461
  | 2 => pEC2A462
  | 3 => pEC2A463
  | 4 => pEC2A468
  | 5 => pEC2A4620
  | 6 => pEC2A469
  | 7 => pEC2A4621
  | 8 => pEC2A464
  | 9 => pEC2A466
  | 10 => pEC2A4616
  | 11 => pEC2A4618
  | 12 => pEC2A4612
  | 13 => pEC2A4613
  | 14 => pEC2A4614
  | 15 => pEC2A4615
  | 16 => pEC2A4610
  | 17 => pEC2A4622
  | 18 => pEC2A4611
  | 19 => pEC2A4623
  | 20 => pEC2A465
  | 21 => pEC2A467
  | 22 => pEC2A4617
  | _ => pEC2A4619

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEC2A46 (i : Fin 24) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permEC2A46 i) (permEinvC2A46 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 5)(1 4)(2 3)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXC2A460 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0
def pXC2A460inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0

def permXC2A46 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXC2A460

def permXinvC2A46 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXC2A460inv

def eXC2A46 (i : Fin 1) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXC2A46 i) (permXinvC2A46 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def repC2A46 : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trC2A46 : Fin 6 → Fin 6 → Fin 4 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (1, 2)
  | 0, 5 => (2, 1)
  | 1, 0 => (2, 4)
  | 1, 1 => (0, 4)
  | 1, 2 => (1, 4)
  | 1, 3 => (2, 5)
  | 1, 4 => (3, 4)
  | 1, 5 => (1, 6)
  | 2, 0 => (1, 8)
  | 2, 1 => (2, 8)
  | 2, 2 => (0, 8)
  | 2, 3 => (1, 10)
  | 2, 4 => (2, 9)
  | 2, 5 => (3, 8)
  | 3, 0 => (3, 12)
  | 3, 1 => (1, 12)
  | 3, 2 => (2, 12)
  | 3, 3 => (0, 12)
  | 3, 4 => (1, 14)
  | 3, 5 => (2, 13)
  | 4, 0 => (2, 16)
  | 4, 1 => (3, 16)
  | 4, 2 => (1, 16)
  | 4, 3 => (2, 17)
  | 4, 4 => (0, 16)
  | 4, 5 => (1, 18)
  | 5, 0 => (1, 20)
  | 5, 1 => (2, 20)
  | 5, 2 => (3, 20)
  | 5, 3 => (1, 22)
  | 5, 4 => (2, 21)
  | 5, 5 => (0, 20)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxC2A460 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valC2A460 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `3`, `4`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdxC2A461 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 1
def valC2A461 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, `3`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdxC2A462 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 2
def valC2A462 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 5

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxC2A463 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valC2A463 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `4` orbit values named by the family's arguments. -/
def decC2A46 (a : Fin 2) (b c : Fin 4) (d : Fin 2) : Fin 4 → Fin 6
  | 0 => valC2A460 a
  | 1 => valC2A461 b
  | 2 => valC2A462 c
  | 3 => valC2A463 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabC2A46_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabC2A46 (a : Fin 2) (b c : Fin 4) (d : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valC2A460 a
  | 0, 1 => valC2A461 b
  | 0, 2 => valC2A462 c
  | 0, 3 => valC2A463 d
  | 0, 4 => pEC2A462 (valC2A461 b)
  | 0, 5 => pEC2A461 (valC2A462 c)
  | 1, 0 => pEC2A464 (valC2A462 c)
  | 1, 1 => pEC2A464 (valC2A460 a)
  | 1, 2 => pEC2A464 (valC2A461 b)
  | 1, 3 => pEC2A465 (valC2A462 c)
  | 1, 4 => pEC2A464 (valC2A463 d)
  | 1, 5 => pEC2A466 (valC2A461 b)
  | 2, 0 => pEC2A468 (valC2A461 b)
  | 2, 1 => pEC2A468 (valC2A462 c)
  | 2, 2 => pEC2A468 (valC2A460 a)
  | 2, 3 => pEC2A4610 (valC2A461 b)
  | 2, 4 => pEC2A469 (valC2A462 c)
  | 2, 5 => pEC2A468 (valC2A463 d)
  | 3, 0 => pEC2A4612 (valC2A463 d)
  | 3, 1 => pEC2A4612 (valC2A461 b)
  | 3, 2 => pEC2A4612 (valC2A462 c)
  | 3, 3 => pEC2A4612 (valC2A460 a)
  | 3, 4 => pEC2A4614 (valC2A461 b)
  | 3, 5 => pEC2A4613 (valC2A462 c)
  | 4, 0 => pEC2A4616 (valC2A462 c)
  | 4, 1 => pEC2A4616 (valC2A463 d)
  | 4, 2 => pEC2A4616 (valC2A461 b)
  | 4, 3 => pEC2A4617 (valC2A462 c)
  | 4, 4 => pEC2A4616 (valC2A460 a)
  | 4, 5 => pEC2A4618 (valC2A461 b)
  | 5, 0 => pEC2A4620 (valC2A461 b)
  | 5, 1 => pEC2A4620 (valC2A462 c)
  | 5, 2 => pEC2A4620 (valC2A463 d)
  | 5, 3 => pEC2A4622 (valC2A461 b)
  | 5, 4 => pEC2A4621 (valC2A462 c)
  | 5, 5 => pEC2A4620 (valC2A460 a)

theorem tabC2A46_eq_transport (a : Fin 2) (b c : Fin 4) (d : Fin 2) :
    tabC2A46 a b c d = Magma.transport permEC2A46 trC2A46 (decC2A46 a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `48` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `64` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowC2A460 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 0 0 1 0
  | 1 => tabC2A46 0 0 1 1
  | 2 => tabC2A46 0 0 2 0
  | 3 => tabC2A46 0 0 2 1
  | 4 => tabC2A46 0 0 3 0
  | 5 => tabC2A46 0 0 3 1
  | _ => tabC2A46 0 1 0 0
def memRowC2A461 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 0 1 0 1
  | 1 => tabC2A46 0 1 2 0
  | 2 => tabC2A46 0 1 2 1
  | 3 => tabC2A46 0 1 3 0
  | 4 => tabC2A46 0 1 3 1
  | 5 => tabC2A46 0 2 0 0
  | _ => tabC2A46 0 2 0 1
def memRowC2A462 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 0 2 1 0
  | 1 => tabC2A46 0 2 1 1
  | 2 => tabC2A46 0 2 3 0
  | 3 => tabC2A46 0 2 3 1
  | 4 => tabC2A46 0 3 0 0
  | 5 => tabC2A46 0 3 0 1
  | _ => tabC2A46 0 3 1 0
def memRowC2A463 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 0 3 1 1
  | 1 => tabC2A46 0 3 2 0
  | 2 => tabC2A46 0 3 2 1
  | 3 => tabC2A46 1 0 1 0
  | 4 => tabC2A46 1 0 1 1
  | 5 => tabC2A46 1 0 2 0
  | _ => tabC2A46 1 0 2 1
def memRowC2A464 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 1 0 3 0
  | 1 => tabC2A46 1 0 3 1
  | 2 => tabC2A46 1 1 0 0
  | 3 => tabC2A46 1 1 0 1
  | 4 => tabC2A46 1 1 2 0
  | 5 => tabC2A46 1 1 2 1
  | _ => tabC2A46 1 1 3 0
def memRowC2A465 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 1 1 3 1
  | 1 => tabC2A46 1 2 0 0
  | 2 => tabC2A46 1 2 0 1
  | 3 => tabC2A46 1 2 1 0
  | 4 => tabC2A46 1 2 1 1
  | 5 => tabC2A46 1 2 3 0
  | _ => tabC2A46 1 2 3 1
def memRowC2A466 : Fin 7 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabC2A46 1 3 0 0
  | 1 => tabC2A46 1 3 0 1
  | 2 => tabC2A46 1 3 1 0
  | 3 => tabC2A46 1 3 1 1
  | 4 => tabC2A46 1 3 2 0
  | _ => tabC2A46 1 3 2 1
def memC2A46 (i : Fin 48) : Fin 6 → Fin 6 → Fin 6 :=
  match (i.1 / 7 : Nat) with
  | 0 => memRowC2A460 ⟨i.1 % 7, by omega⟩
  | 1 => memRowC2A461 ⟨i.1 % 7, by omega⟩
  | 2 => memRowC2A462 ⟨i.1 % 7, by omega⟩
  | 3 => memRowC2A463 ⟨i.1 % 7, by omega⟩
  | 4 => memRowC2A464 ⟨i.1 % 7, by omega⟩
  | 5 => memRowC2A465 ⟨i.1 % 7, by omega⟩
  | _ => memRowC2A466 ⟨i.1 % 7, by omega⟩

/-- Which of the `48` members a given invariant tuple is, so that `mem_of_isExactC2A46` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrC2A46 : Array Nat := #[
  0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 16, 17, 18, 19, 20, 21,
  22, 23, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0,
  40, 41, 42, 43, 44, 45, 46, 47, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArrC2A46` is addressed. -/
def encTC2A46 (a : Fin 2) (b c : Fin 4) (d : Fin 2) : Nat :=
  a.1 * 32 +
    b.1 * 8 +
    c.1 * 2 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankC2A46 (a : Fin 2) (b c : Fin 4) (d : Fin 2) : Fin 48 :=
  ⟨min (rankArrC2A46.getD (encTC2A46 a b c d) 0) 47, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactC2A46 (i : Fin 48) : Magma (Fin 6) := Magma.mk (memC2A46 i)

theorem exactC2A46_isEndo (i : Fin 48) (j : Fin 24) : (exactC2A46 i).IsEndo ⇑(eEC2A46 j) := by
  simp only [eEC2A46, coe_permOf]; revert i j; native_decide

theorem exactC2A46_not_isEndo (i : Fin 48) (j : Fin 1) : ¬ (exactC2A46 i).IsEndo ⇑(eXC2A46 j) := by
  simp only [eXC2A46, coe_permOf]; revert i j; native_decide

/-- `rankC2A46` really does name the member a tuple is. Deciding this is one array read and one
table comparison per tuple, where searching `memC2A46` for the index would be a comparison per tuple
and member. -/
theorem mem_rankC2A46 (a : Fin 2) (b c : Fin 4) (d : Fin 2)
    (h : Magma.isExact (tabC2A46 a b c d) permEC2A46 permXC2A46 = true) :
    memC2A46 (rankC2A46 a b c d) = tabC2A46 a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `48` listed
members. -/
theorem mem_of_isExactC2A46 (a : Fin 2) (b c : Fin 4) (d : Fin 2)
    (h : Magma.isExact (tabC2A46 a b c d) permEC2A46 permXC2A46 = true) :
    ∃ i, memC2A46 i = tabC2A46 a b c d :=
  ⟨_, mem_rankC2A46 a b c d h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactC2A46`. Its values at the orbit representatives name an invariant
tuple, and `mem_of_isExactC2A46` turns that into a member index. -/
theorem exists_exactC2A46 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eEC2A46 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXC2A46 i)) : ∃ i, exactC2A46 i = M := by
  simp only [eEC2A46, coe_permOf] at hE
  simp only [eXC2A46, coe_permOf] at hX
  have hop : M.op =
      Magma.transport permEC2A46 trC2A46 (fun i ↦ M.op (repC2A46 i).1 (repC2A46 i).2) :=
    Magma.op_eq_transport (rep := repC2A46) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A46) (idx := stabIdxC2A460) (a := (repC2A46 0).1) (b := (repC2A46 0).2)
    (val := valC2A460) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A46) (idx := stabIdxC2A461) (a := (repC2A46 1).1) (b := (repC2A46 1).2)
    (val := valC2A461) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A46) (idx := stabIdxC2A462) (a := (repC2A46 2).1) (b := (repC2A46 2).2)
    (val := valC2A462) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEC2A46) (idx := stabIdxC2A463) (a := (repC2A46 3).1) (b := (repC2A46 3).2)
    (val := valC2A463) hE (by decide) (by decide)
  have hdec : decC2A46 a b c d = fun i ↦ M.op (repC2A46 i).1 (repC2A46 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tabC2A46 a b c d = M.op := by
    rw [tabC2A46_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabC2A46 a b c d) permEC2A46 permXC2A46 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactC2A46 a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`24` group of `Magma.permEC2A46`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactC2A46 {L L' : Law.NatMagmaLaw} {i : Fin 48}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactC2A46 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactC2A46 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactC2A46 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactC2A46
    (fun k ↦ (Magma.exactC2A46_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactC2A46_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
