import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D65` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`12` group `⟨(0 1 4)(2 3), (1 4)(2 3)⟩` -/

/-- The `12` elements of the group: `()`, `(2 3)`, `(1 4)`, `(1 4)(2 3)`, `(0 1)`, `(0 1)(2 3)`, `(0
1 4)`, `(0 1 4)(2 3)`, `(0 4 1)`, `(0 4 1)(2 3)`, `(0 4)`, `(0 4)(2 3)`. -/
def pED650 : Fin 5 → Fin 5 := id
def pED651 : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4
def pED652 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1
def pED653 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1
def pED654 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4
def pED655 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4
def pED656 : Fin 5 → Fin 5 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0
def pED657 : Fin 5 → Fin 5 | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0
def pED658 : Fin 5 → Fin 5 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1
def pED659 : Fin 5 → Fin 5 | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1
def pED6510 : Fin 5 → Fin 5 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0
def pED6511 : Fin 5 → Fin 5 | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0

def permED65 : Fin 12 → Fin 5 → Fin 5
  | 0 => pED650
  | 1 => pED651
  | 2 => pED652
  | 3 => pED653
  | 4 => pED654
  | 5 => pED655
  | 6 => pED656
  | 7 => pED657
  | 8 => pED658
  | 9 => pED659
  | 10 => pED6510
  | 11 => pED6511

def permEinvD65 : Fin 12 → Fin 5 → Fin 5
  | 0 => pED650
  | 1 => pED651
  | 2 => pED652
  | 3 => pED653
  | 4 => pED654
  | 5 => pED655
  | 6 => pED658
  | 7 => pED659
  | 8 => pED656
  | 9 => pED657
  | 10 => pED6510
  | 11 => pED6511

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED65 (i : Fin 12) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permED65 i) (permEinvD65 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3)`. Every subgroup properly containing
the group above contains it, so a magma admitting the group and not this has that group as its
automorphism group exactly. -/
def pXD650 : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4
def pXD650inv : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4

def permXD65 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXD650

def permXinvD65 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXD650inv

def eXD65 (i : Fin 1) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXD65 i) (permXinvD65 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `6`, so an invariant
operation is `6` values. -/
def repD65 : Fin 6 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (2, 0)
  | 4 => (2, 2)
  | 5 => (2, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD65 : Fin 5 → Fin 5 → Fin 6 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 0, 4 => (1, 2)
  | 1, 0 => (1, 4)
  | 1, 1 => (0, 4)
  | 1, 2 => (2, 4)
  | 1, 3 => (2, 5)
  | 1, 4 => (1, 6)
  | 2, 0 => (3, 0)
  | 2, 1 => (3, 4)
  | 2, 2 => (4, 0)
  | 2, 3 => (5, 0)
  | 2, 4 => (3, 8)
  | 3, 0 => (3, 1)
  | 3, 1 => (3, 5)
  | 3, 2 => (5, 1)
  | 3, 3 => (4, 1)
  | 3, 4 => (3, 9)
  | 4, 0 => (1, 8)
  | 4, 1 => (1, 10)
  | 4, 2 => (2, 8)
  | 4, 3 => (2, 9)
  | 4, 4 => (0, 8)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxD650 : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valD650 : Fin 1 → Fin 5
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `4`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD651 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def valD651 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 4

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, `3`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD652 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 2
def valD652 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 2
  | 2 => 3

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `2`, `3`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxD653 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 2
def valD653 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 2
  | 2 => 3

/-- The `6` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD654 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 10
def valD654 : Fin 2 → Fin 5
  | 0 => 2
  | 1 => 3

/-- The `6` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `2`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD655 : Fin 6 → Fin 12
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 10
def valD655 : Fin 2 → Fin 5
  | 0 => 2
  | 1 => 3

/-- The `6` orbit values named by the family's arguments. -/
def decD65 (a : Fin 1) (b c d : Fin 3) (e f : Fin 2) : Fin 6 → Fin 5
  | 0 => valD650 a
  | 1 => valD651 b
  | 2 => valD652 c
  | 3 => valD653 d
  | 4 => valD654 e
  | 5 => valD655 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD65_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD65 (a : Fin 1) (b c d : Fin 3) (e f : Fin 2) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valD650 a
  | 0, 1 => valD651 b
  | 0, 2 => valD652 c
  | 0, 3 => pED651 (valD652 c)
  | 0, 4 => pED652 (valD651 b)
  | 1, 0 => pED654 (valD651 b)
  | 1, 1 => pED654 (valD650 a)
  | 1, 2 => pED654 (valD652 c)
  | 1, 3 => pED655 (valD652 c)
  | 1, 4 => pED656 (valD651 b)
  | 2, 0 => valD653 d
  | 2, 1 => pED654 (valD653 d)
  | 2, 2 => valD654 e
  | 2, 3 => valD655 f
  | 2, 4 => pED658 (valD653 d)
  | 3, 0 => pED651 (valD653 d)
  | 3, 1 => pED655 (valD653 d)
  | 3, 2 => pED651 (valD655 f)
  | 3, 3 => pED651 (valD654 e)
  | 3, 4 => pED659 (valD653 d)
  | 4, 0 => pED658 (valD651 b)
  | 4, 1 => pED6510 (valD651 b)
  | 4, 2 => pED658 (valD652 c)
  | 4, 3 => pED659 (valD652 c)
  | 4, 4 => pED658 (valD650 a)

theorem tabD65_eq_transport (a : Fin 1) (b c d : Fin 3) (e f : Fin 2) :
    tabD65 a b c d e f = Magma.transport permED65 trD65 (decD65 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `106` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `108` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowD650 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 0 0 0 0 0
  | 1 => tabD65 0 0 0 0 0 1
  | 2 => tabD65 0 0 0 0 1 0
  | 3 => tabD65 0 0 0 0 1 1
  | 4 => tabD65 0 0 0 1 0 1
  | 5 => tabD65 0 0 0 1 1 0
  | 6 => tabD65 0 0 0 1 1 1
  | 7 => tabD65 0 0 0 2 0 0
  | 8 => tabD65 0 0 0 2 0 1
  | 9 => tabD65 0 0 0 2 1 0
  | _ => tabD65 0 0 0 2 1 1
def memRowD651 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 0 1 0 0 0
  | 1 => tabD65 0 0 1 0 0 1
  | 2 => tabD65 0 0 1 0 1 0
  | 3 => tabD65 0 0 1 0 1 1
  | 4 => tabD65 0 0 1 1 0 0
  | 5 => tabD65 0 0 1 1 0 1
  | 6 => tabD65 0 0 1 1 1 0
  | 7 => tabD65 0 0 1 1 1 1
  | 8 => tabD65 0 0 1 2 0 0
  | 9 => tabD65 0 0 1 2 0 1
  | _ => tabD65 0 0 1 2 1 0
def memRowD652 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 0 1 2 1 1
  | 1 => tabD65 0 0 2 0 0 0
  | 2 => tabD65 0 0 2 0 0 1
  | 3 => tabD65 0 0 2 0 1 0
  | 4 => tabD65 0 0 2 0 1 1
  | 5 => tabD65 0 0 2 1 0 0
  | 6 => tabD65 0 0 2 1 0 1
  | 7 => tabD65 0 0 2 1 1 0
  | 8 => tabD65 0 0 2 1 1 1
  | 9 => tabD65 0 0 2 2 0 0
  | _ => tabD65 0 0 2 2 0 1
def memRowD653 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 0 2 2 1 0
  | 1 => tabD65 0 0 2 2 1 1
  | 2 => tabD65 0 1 0 0 0 0
  | 3 => tabD65 0 1 0 0 0 1
  | 4 => tabD65 0 1 0 0 1 0
  | 5 => tabD65 0 1 0 0 1 1
  | 6 => tabD65 0 1 0 1 0 0
  | 7 => tabD65 0 1 0 1 0 1
  | 8 => tabD65 0 1 0 1 1 0
  | 9 => tabD65 0 1 0 1 1 1
  | _ => tabD65 0 1 0 2 0 0
def memRowD654 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 1 0 2 0 1
  | 1 => tabD65 0 1 0 2 1 0
  | 2 => tabD65 0 1 0 2 1 1
  | 3 => tabD65 0 1 1 0 0 0
  | 4 => tabD65 0 1 1 0 1 0
  | 5 => tabD65 0 1 1 0 1 1
  | 6 => tabD65 0 1 1 1 0 0
  | 7 => tabD65 0 1 1 1 0 1
  | 8 => tabD65 0 1 1 1 1 0
  | 9 => tabD65 0 1 1 1 1 1
  | _ => tabD65 0 1 1 2 0 0
def memRowD655 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 1 1 2 0 1
  | 1 => tabD65 0 1 1 2 1 0
  | 2 => tabD65 0 1 1 2 1 1
  | 3 => tabD65 0 1 2 0 0 0
  | 4 => tabD65 0 1 2 0 0 1
  | 5 => tabD65 0 1 2 0 1 0
  | 6 => tabD65 0 1 2 0 1 1
  | 7 => tabD65 0 1 2 1 0 0
  | 8 => tabD65 0 1 2 1 0 1
  | 9 => tabD65 0 1 2 1 1 0
  | _ => tabD65 0 1 2 1 1 1
def memRowD656 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 1 2 2 0 0
  | 1 => tabD65 0 1 2 2 0 1
  | 2 => tabD65 0 1 2 2 1 0
  | 3 => tabD65 0 1 2 2 1 1
  | 4 => tabD65 0 2 0 0 0 0
  | 5 => tabD65 0 2 0 0 0 1
  | 6 => tabD65 0 2 0 0 1 0
  | 7 => tabD65 0 2 0 0 1 1
  | 8 => tabD65 0 2 0 1 0 0
  | 9 => tabD65 0 2 0 1 0 1
  | _ => tabD65 0 2 0 1 1 0
def memRowD657 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 2 0 1 1 1
  | 1 => tabD65 0 2 0 2 0 0
  | 2 => tabD65 0 2 0 2 0 1
  | 3 => tabD65 0 2 0 2 1 0
  | 4 => tabD65 0 2 0 2 1 1
  | 5 => tabD65 0 2 1 0 0 0
  | 6 => tabD65 0 2 1 0 0 1
  | 7 => tabD65 0 2 1 0 1 0
  | 8 => tabD65 0 2 1 0 1 1
  | 9 => tabD65 0 2 1 1 0 0
  | _ => tabD65 0 2 1 1 0 1
def memRowD658 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 2 1 1 1 0
  | 1 => tabD65 0 2 1 1 1 1
  | 2 => tabD65 0 2 1 2 0 0
  | 3 => tabD65 0 2 1 2 0 1
  | 4 => tabD65 0 2 1 2 1 0
  | 5 => tabD65 0 2 1 2 1 1
  | 6 => tabD65 0 2 2 0 0 0
  | 7 => tabD65 0 2 2 0 0 1
  | 8 => tabD65 0 2 2 0 1 0
  | 9 => tabD65 0 2 2 0 1 1
  | _ => tabD65 0 2 2 1 0 0
def memRowD659 : Fin 11 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD65 0 2 2 1 0 1
  | 1 => tabD65 0 2 2 1 1 0
  | 2 => tabD65 0 2 2 1 1 1
  | 3 => tabD65 0 2 2 2 0 0
  | 4 => tabD65 0 2 2 2 0 1
  | 5 => tabD65 0 2 2 2 1 0
  | _ => tabD65 0 2 2 2 1 1
def memD65 (i : Fin 106) : Fin 5 → Fin 5 → Fin 5 :=
  match (i.1 / 11 : Nat) with
  | 0 => memRowD650 ⟨i.1 % 11, by omega⟩
  | 1 => memRowD651 ⟨i.1 % 11, by omega⟩
  | 2 => memRowD652 ⟨i.1 % 11, by omega⟩
  | 3 => memRowD653 ⟨i.1 % 11, by omega⟩
  | 4 => memRowD654 ⟨i.1 % 11, by omega⟩
  | 5 => memRowD655 ⟨i.1 % 11, by omega⟩
  | 6 => memRowD656 ⟨i.1 % 11, by omega⟩
  | 7 => memRowD657 ⟨i.1 % 11, by omega⟩
  | 8 => memRowD658 ⟨i.1 % 11, by omega⟩
  | _ => memRowD659 ⟨i.1 % 11, by omega⟩

/-- Which of the `106` members a given invariant tuple is, so that `mem_of_isExactD65` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD65 : Array Nat := #[
  0, 1, 2, 3, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 0,
  48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
  72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
  96, 97, 98, 99, 100, 101, 102, 103, 104, 105]

/-- The arguments as one mixed-radix index, which is how `rankArrD65` is addressed. -/
def encTD65 (a : Fin 1) (b c d : Fin 3) (e f : Fin 2) : Nat :=
  a.1 * 108 +
    b.1 * 36 +
    c.1 * 12 +
    d.1 * 4 +
    e.1 * 2 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD65 (a : Fin 1) (b c d : Fin 3) (e f : Fin 2) : Fin 106 :=
  ⟨min (rankArrD65.getD (encTD65 a b c d e f) 0) 105, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD65 (i : Fin 106) : Magma (Fin 5) := Magma.mk (memD65 i)

theorem exactD65_isEndo (i : Fin 106) (j : Fin 12) : (exactD65 i).IsEndo ⇑(eED65 j) := by
  simp only [eED65, coe_permOf]; revert i j; native_decide

theorem exactD65_not_isEndo (i : Fin 106) (j : Fin 1) : ¬ (exactD65 i).IsEndo ⇑(eXD65 j) := by
  simp only [eXD65, coe_permOf]; revert i j; native_decide

/-- `rankD65` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD65` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD65 (a : Fin 1) (b c d : Fin 3) (e f : Fin 2)
    (h : Magma.isExact (tabD65 a b c d e f) permED65 permXD65 = true) :
    memD65 (rankD65 a b c d e f) = tabD65 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `106`
listed members. -/
theorem mem_of_isExactD65 (a : Fin 1) (b c d : Fin 3) (e f : Fin 2)
    (h : Magma.isExact (tabD65 a b c d e f) permED65 permXD65 = true) :
    ∃ i, memD65 i = tabD65 a b c d e f :=
  ⟨_, mem_rankD65 a b c d e f h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD65`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD65` turns that into a member index. -/
theorem exists_exactD65 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eED65 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD65 i)) : ∃ i, exactD65 i = M := by
  simp only [eED65, coe_permOf] at hE
  simp only [eXD65, coe_permOf] at hX
  have hop : M.op = Magma.transport permED65 trD65 (fun i ↦ M.op (repD65 i).1 (repD65 i).2) :=
    Magma.op_eq_transport (rep := repD65) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED65) (idx := stabIdxD650) (a := (repD65 0).1) (b := (repD65 0).2)
    (val := valD650) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED65) (idx := stabIdxD651) (a := (repD65 1).1) (b := (repD65 1).2)
    (val := valD651) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED65) (idx := stabIdxD652) (a := (repD65 2).1) (b := (repD65 2).2)
    (val := valD652) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permED65) (idx := stabIdxD653) (a := (repD65 3).1) (b := (repD65 3).2)
    (val := valD653) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permED65) (idx := stabIdxD654) (a := (repD65 4).1) (b := (repD65 4).2)
    (val := valD654) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permED65) (idx := stabIdxD655) (a := (repD65 5).1) (b := (repD65 5).2)
    (val := valD655) hE (by decide) (by decide)
  have hdec : decD65 a b c d e f = fun i ↦ M.op (repD65 i).1 (repD65 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabD65 a b c d e f = M.op := by
    rw [tabD65_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD65 a b c d e f) permED65 permXD65 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD65 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`12` group of `Magma.permED65`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD65 {L L' : Law.NatMagmaLaw} {i : Fin 106}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactD65 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactD65 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD65 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD65
    (fun k ↦ (Magma.exactD65_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD65_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
