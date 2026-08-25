import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `A46` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`12` group `⟨(0 1 2)(3 4 5), (0 1 5)(2 3 4)⟩` -/

/-- The `12` elements of the group: `()`, `(1 4)(2 5)`, `(0 1 2)(3 4 5)`, `(0 1 5)(2 3 4)`, `(0 2
1)(3 5 4)`, `(0 2 4)(1 3 5)`, `(0 3)(2 5)`, `(0 3)(1 4)`, `(0 4 5)(1 2 3)`, `(0 4 2)(1 5 3)`, `(0 5
1)(2 4 3)`, `(0 5 4)(1 3 2)`. -/
def pEA460 : Fin 6 → Fin 6 := id
def pEA461 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 2
def pEA462 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pEA463 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 0
def pEA464 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pEA465 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 1
def pEA466 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 2
def pEA467 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5
def pEA468 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0
def pEA469 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3
def pEA4610 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1
def pEA4611 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4

def permEA46 : Fin 12 → Fin 6 → Fin 6
  | 0 => pEA460
  | 1 => pEA461
  | 2 => pEA462
  | 3 => pEA463
  | 4 => pEA464
  | 5 => pEA465
  | 6 => pEA466
  | 7 => pEA467
  | 8 => pEA468
  | 9 => pEA469
  | 10 => pEA4610
  | 11 => pEA4611

def permEinvA46 : Fin 12 → Fin 6 → Fin 6
  | 0 => pEA460
  | 1 => pEA461
  | 2 => pEA464
  | 3 => pEA4610
  | 4 => pEA462
  | 5 => pEA469
  | 6 => pEA466
  | 7 => pEA467
  | 8 => pEA4611
  | 9 => pEA465
  | 10 => pEA463
  | 11 => pEA468

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEA46 (i : Fin 12) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permEA46 i) (permEinvA46 i) (by revert i; decide)

/-- The `5` permutations that must *not* be automorphisms: `(1 5 3 2 4)`, `(1 5)(2 4)`, `(0 4 3 5
2)`, `(0 4 2 3 1 5)`, `(0 5)(1 4)(2 3)`. Every subgroup properly containing the group above contains
one of them, so a magma admitting the group and not these has that group as its automorphism group
exactly. -/
def pXA460 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 3
def pXA461 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1
def pXA462 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 2
def pXA463 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 0
def pXA464 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0
def pXA460inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 5 | 4 => 2 | 5 => 1
def pXA461inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1
def pXA462inv : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 3
def pXA463inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 1
def pXA464inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0

def permXA46 : Fin 5 → Fin 6 → Fin 6
  | 0 => pXA460
  | 1 => pXA461
  | 2 => pXA462
  | 3 => pXA463
  | 4 => pXA464

def permXinvA46 : Fin 5 → Fin 6 → Fin 6
  | 0 => pXA460inv
  | 1 => pXA461inv
  | 2 => pXA462inv
  | 3 => pXA463inv
  | 4 => pXA464inv

def eXA46 (i : Fin 5) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXA46 i) (permXinvA46 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def repA46 : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trA46 : Fin 6 → Fin 6 → Fin 4 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (1, 1)
  | 0, 5 => (2, 1)
  | 1, 0 => (2, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 2)
  | 1, 3 => (2, 3)
  | 1, 4 => (3, 2)
  | 1, 5 => (1, 3)
  | 2, 0 => (1, 4)
  | 2, 1 => (2, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (1, 5)
  | 2, 4 => (2, 5)
  | 2, 5 => (3, 4)
  | 3, 0 => (3, 6)
  | 3, 1 => (1, 6)
  | 3, 2 => (2, 7)
  | 3, 3 => (0, 6)
  | 3, 4 => (1, 7)
  | 3, 5 => (2, 6)
  | 4, 0 => (2, 9)
  | 4, 1 => (3, 8)
  | 4, 2 => (1, 8)
  | 4, 3 => (2, 8)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 9)
  | 5, 0 => (1, 10)
  | 5, 1 => (2, 11)
  | 5, 2 => (3, 10)
  | 5, 3 => (1, 11)
  | 5, 4 => (2, 10)
  | 5, 5 => (0, 10)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxA460 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def valA460 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxA461 : Fin 1 → Fin 12
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxA462 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxA463 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def valA463 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `4` orbit values named by the family's arguments. -/
def decA46 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 4 → Fin 6
  | 0 => valA460 a
  | 1 => b
  | 2 => c
  | 3 => valA463 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabA46_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabA46 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valA460 a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => valA463 d
  | 0, 4 => pEA461 b
  | 0, 5 => pEA461 c
  | 1, 0 => pEA462 c
  | 1, 1 => pEA462 (valA460 a)
  | 1, 2 => pEA462 b
  | 1, 3 => pEA463 c
  | 1, 4 => pEA462 (valA463 d)
  | 1, 5 => pEA463 b
  | 2, 0 => pEA464 b
  | 2, 1 => pEA464 c
  | 2, 2 => pEA464 (valA460 a)
  | 2, 3 => pEA465 b
  | 2, 4 => pEA465 c
  | 2, 5 => pEA464 (valA463 d)
  | 3, 0 => pEA466 (valA463 d)
  | 3, 1 => pEA466 b
  | 3, 2 => pEA467 c
  | 3, 3 => pEA466 (valA460 a)
  | 3, 4 => pEA467 b
  | 3, 5 => pEA466 c
  | 4, 0 => pEA469 c
  | 4, 1 => pEA468 (valA463 d)
  | 4, 2 => pEA468 b
  | 4, 3 => pEA468 c
  | 4, 4 => pEA468 (valA460 a)
  | 4, 5 => pEA469 b
  | 5, 0 => pEA4610 b
  | 5, 1 => pEA4611 c
  | 5, 2 => pEA4610 (valA463 d)
  | 5, 3 => pEA4611 b
  | 5, 4 => pEA4610 c
  | 5, 5 => pEA4610 (valA460 a)

theorem tabA46_eq_transport (a : Fin 2) (b c : Fin 6) (d : Fin 2) :
    tabA46 a b c d = Magma.transport permEA46 trA46 (decA46 a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `64` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `144` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowA460 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 0 0 1 0
  | 1 => tabA46 0 0 1 1
  | 2 => tabA46 0 0 4 0
  | 3 => tabA46 0 0 4 1
  | 4 => tabA46 0 1 1 0
  | 5 => tabA46 0 1 1 1
  | 6 => tabA46 0 1 4 0
  | _ => tabA46 0 1 4 1
def memRowA461 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 0 2 0 0
  | 1 => tabA46 0 2 0 1
  | 2 => tabA46 0 2 2 0
  | 3 => tabA46 0 2 2 1
  | 4 => tabA46 0 2 3 0
  | 5 => tabA46 0 2 3 1
  | 6 => tabA46 0 2 5 0
  | _ => tabA46 0 2 5 1
def memRowA462 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 0 3 1 0
  | 1 => tabA46 0 3 1 1
  | 2 => tabA46 0 3 4 0
  | 3 => tabA46 0 3 4 1
  | 4 => tabA46 0 4 1 0
  | 5 => tabA46 0 4 1 1
  | 6 => tabA46 0 4 4 0
  | _ => tabA46 0 4 4 1
def memRowA463 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 0 5 0 0
  | 1 => tabA46 0 5 0 1
  | 2 => tabA46 0 5 2 0
  | 3 => tabA46 0 5 2 1
  | 4 => tabA46 0 5 3 0
  | 5 => tabA46 0 5 3 1
  | 6 => tabA46 0 5 5 0
  | _ => tabA46 0 5 5 1
def memRowA464 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 1 0 1 0
  | 1 => tabA46 1 0 1 1
  | 2 => tabA46 1 0 4 0
  | 3 => tabA46 1 0 4 1
  | 4 => tabA46 1 1 1 0
  | 5 => tabA46 1 1 1 1
  | 6 => tabA46 1 1 4 0
  | _ => tabA46 1 1 4 1
def memRowA465 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 1 2 0 0
  | 1 => tabA46 1 2 0 1
  | 2 => tabA46 1 2 2 0
  | 3 => tabA46 1 2 2 1
  | 4 => tabA46 1 2 3 0
  | 5 => tabA46 1 2 3 1
  | 6 => tabA46 1 2 5 0
  | _ => tabA46 1 2 5 1
def memRowA466 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 1 3 1 0
  | 1 => tabA46 1 3 1 1
  | 2 => tabA46 1 3 4 0
  | 3 => tabA46 1 3 4 1
  | 4 => tabA46 1 4 1 0
  | 5 => tabA46 1 4 1 1
  | 6 => tabA46 1 4 4 0
  | _ => tabA46 1 4 4 1
def memRowA467 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabA46 1 5 0 0
  | 1 => tabA46 1 5 0 1
  | 2 => tabA46 1 5 2 0
  | 3 => tabA46 1 5 2 1
  | 4 => tabA46 1 5 3 0
  | 5 => tabA46 1 5 3 1
  | 6 => tabA46 1 5 5 0
  | _ => tabA46 1 5 5 1
def memA46 (i : Fin 64) : Fin 6 → Fin 6 → Fin 6 :=
  match (i.1 / 8 : Nat) with
  | 0 => memRowA460 ⟨i.1 % 8, by omega⟩
  | 1 => memRowA461 ⟨i.1 % 8, by omega⟩
  | 2 => memRowA462 ⟨i.1 % 8, by omega⟩
  | 3 => memRowA463 ⟨i.1 % 8, by omega⟩
  | 4 => memRowA464 ⟨i.1 % 8, by omega⟩
  | 5 => memRowA465 ⟨i.1 % 8, by omega⟩
  | 6 => memRowA466 ⟨i.1 % 8, by omega⟩
  | _ => memRowA467 ⟨i.1 % 8, by omega⟩

/-- Which of the `64` members a given invariant tuple is, so that `mem_of_isExactA46` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrA46 : Array Nat := #[
  0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 4, 5, 0, 0, 0, 0, 6, 7, 0, 0, 8, 9, 0, 0, 10, 11, 12,
  13, 0, 0, 14, 15, 0, 0, 16, 17, 0, 0, 0, 0, 18, 19, 0, 0, 0, 0, 20, 21, 0, 0, 0, 0, 22, 23, 0,
  0, 24, 25, 0, 0, 26, 27, 28, 29, 0, 0, 30, 31, 0, 0, 32, 33, 0, 0, 0, 0, 34, 35, 0, 0, 0, 0,
  36, 37, 0, 0, 0, 0, 38, 39, 0, 0, 40, 41, 0, 0, 42, 43, 44, 45, 0, 0, 46, 47, 0, 0, 48, 49, 0,
  0, 0, 0, 50, 51, 0, 0, 0, 0, 52, 53, 0, 0, 0, 0, 54, 55, 0, 0, 56, 57, 0, 0, 58, 59, 60, 61, 0,
  0, 62, 63]

/-- The arguments as one mixed-radix index, which is how `rankArrA46` is addressed. -/
def encTA46 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Nat :=
  a.1 * 72 +
    b.1 * 12 +
    c.1 * 2 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankA46 (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 64 :=
  ⟨min (rankArrA46.getD (encTA46 a b c d) 0) 63, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactA46 (i : Fin 64) : Magma (Fin 6) := Magma.mk (memA46 i)

theorem exactA46_isEndo (i : Fin 64) (j : Fin 12) : (exactA46 i).IsEndo ⇑(eEA46 j) := by
  simp only [eEA46, coe_permOf]; revert i j; native_decide

theorem exactA46_not_isEndo (i : Fin 64) (j : Fin 5) : ¬ (exactA46 i).IsEndo ⇑(eXA46 j) := by
  simp only [eXA46, coe_permOf]; revert i j; native_decide

/-- `rankA46` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memA46` for the index would be a comparison per tuple and
member. -/
theorem mem_rankA46 (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tabA46 a b c d) permEA46 permXA46 = true) :
    memA46 (rankA46 a b c d) = tabA46 a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `64` listed
members. -/
theorem mem_of_isExactA46 (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tabA46 a b c d) permEA46 permXA46 = true) :
    ∃ i, memA46 i = tabA46 a b c d :=
  ⟨_, mem_rankA46 a b c d h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactA46`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactA46` turns that into a member index. -/
theorem exists_exactA46 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eEA46 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXA46 i)) : ∃ i, exactA46 i = M := by
  simp only [eEA46, coe_permOf] at hE
  simp only [eXA46, coe_permOf] at hX
  have hop : M.op = Magma.transport permEA46 trA46 (fun i ↦ M.op (repA46 i).1 (repA46 i).2) :=
    Magma.op_eq_transport (rep := repA46) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEA46) (idx := stabIdxA460) (a := (repA46 0).1) (b := (repA46 0).2)
    (val := valA460) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEA46) (idx := stabIdxA461) (a := (repA46 1).1) (b := (repA46 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEA46) (idx := stabIdxA462) (a := (repA46 2).1) (b := (repA46 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEA46) (idx := stabIdxA463) (a := (repA46 3).1) (b := (repA46 3).2)
    (val := valA463) hE (by decide) (by decide)
  have hdec : decA46 a b c d = fun i ↦ M.op (repA46 i).1 (repA46 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tabA46 a b c d = M.op := by
    rw [tabA46_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabA46 a b c d) permEA46 permXA46 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactA46 a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`12` group of `Magma.permEA46`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactA46 {L L' : Law.NatMagmaLaw} {i : Fin 64}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactA46 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactA46 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactA46 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactA46
    (fun k ↦ (Magma.exactA46_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactA46_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
