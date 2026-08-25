import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S45` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 1)(2 3), (0 1 2 3), (0 1 3 2)⟩` -/

/-- The `24` elements of the group: `()`, `(2 3)`, `(1 2)`, `(1 2 3)`, `(1 3 2)`, `(1 3)`, `(0 1)`,
`(0 1)(2 3)`, `(0 1 2)`, `(0 1 2 3)`, `(0 1 3 2)`, `(0 1 3)`, `(0 2 1)`, `(0 2 3 1)`, `(0 2)`, `(0 2
3)`, `(0 2)(1 3)`, `(0 2 1 3)`, `(0 3 2 1)`, `(0 3 1)`, `(0 3 2)`, `(0 3)`, `(0 3 1 2)`, `(0 3)(1
2)`. -/
def pES450 : Fin 5 → Fin 5 := id
def pES451 : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4
def pES452 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4
def pES453 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4
def pES454 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4
def pES455 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4
def pES456 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4
def pES457 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4
def pES458 : Fin 5 → Fin 5 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4
def pES459 : Fin 5 → Fin 5 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4
def pES4510 : Fin 5 → Fin 5 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4
def pES4511 : Fin 5 → Fin 5 | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4
def pES4512 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4
def pES4513 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4
def pES4514 : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4
def pES4515 : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4
def pES4516 : Fin 5 → Fin 5 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4
def pES4517 : Fin 5 → Fin 5 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4
def pES4518 : Fin 5 → Fin 5 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4
def pES4519 : Fin 5 → Fin 5 | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4
def pES4520 : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4
def pES4521 : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4
def pES4522 : Fin 5 → Fin 5 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4
def pES4523 : Fin 5 → Fin 5 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4

def permES45 : Fin 24 → Fin 5 → Fin 5
  | 0 => pES450
  | 1 => pES451
  | 2 => pES452
  | 3 => pES453
  | 4 => pES454
  | 5 => pES455
  | 6 => pES456
  | 7 => pES457
  | 8 => pES458
  | 9 => pES459
  | 10 => pES4510
  | 11 => pES4511
  | 12 => pES4512
  | 13 => pES4513
  | 14 => pES4514
  | 15 => pES4515
  | 16 => pES4516
  | 17 => pES4517
  | 18 => pES4518
  | 19 => pES4519
  | 20 => pES4520
  | 21 => pES4521
  | 22 => pES4522
  | _ => pES4523

def permEinvS45 : Fin 24 → Fin 5 → Fin 5
  | 0 => pES450
  | 1 => pES451
  | 2 => pES452
  | 3 => pES454
  | 4 => pES453
  | 5 => pES455
  | 6 => pES456
  | 7 => pES457
  | 8 => pES4512
  | 9 => pES4518
  | 10 => pES4513
  | 11 => pES4519
  | 12 => pES458
  | 13 => pES4510
  | 14 => pES4514
  | 15 => pES4520
  | 16 => pES4516
  | 17 => pES4522
  | 18 => pES459
  | 19 => pES4511
  | 20 => pES4515
  | 21 => pES4521
  | 22 => pES4517
  | _ => pES4523

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES45 (i : Fin 24) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permES45 i) (permEinvS45 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 4 3 2)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXS450 : Fin 5 → Fin 5 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 3
def pXS450inv : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 0

def permXS45 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXS450

def permXinvS45 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXS450inv

def eXS45 (i : Fin 1) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXS45 i) (permXinvS45 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `5`, so an invariant
operation is `5` values. -/
def repS45 : Fin 5 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 4)
  | 3 => (4, 0)
  | 4 => (4, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS45 : Fin 5 → Fin 5 → Fin 5 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 2)
  | 0, 3 => (1, 4)
  | 0, 4 => (2, 0)
  | 1, 0 => (1, 6)
  | 1, 1 => (0, 6)
  | 1, 2 => (1, 8)
  | 1, 3 => (1, 10)
  | 1, 4 => (2, 6)
  | 2, 0 => (1, 12)
  | 2, 1 => (1, 14)
  | 2, 2 => (0, 12)
  | 2, 3 => (1, 16)
  | 2, 4 => (2, 12)
  | 3, 0 => (1, 18)
  | 3, 1 => (1, 20)
  | 3, 2 => (1, 22)
  | 3, 3 => (0, 18)
  | 3, 4 => (2, 18)
  | 4, 0 => (3, 0)
  | 4, 1 => (3, 6)
  | 4, 2 => (3, 12)
  | 4, 3 => (3, 18)
  | 4, 4 => (4, 0)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS450 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS450 : Fin 2 → Fin 5
  | 0 => 0
  | 1 => 4

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `4`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS451 : Fin 2 → Fin 24
  | 0 => 0
  | 1 => 1
def valS451 : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 4

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS452 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS452 : Fin 2 → Fin 5
  | 0 => 0
  | 1 => 4

/-- The `6` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS453 : Fin 6 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS453 : Fin 2 → Fin 5
  | 0 => 0
  | 1 => 4

/-- The `24` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be `4`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS454 : Fin 24 → Fin 24
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
def valS454 : Fin 1 → Fin 5
  | 0 => 4

/-- The `5` orbit values named by the family's arguments. -/
def decS45 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Fin 5 → Fin 5
  | 0 => valS450 a
  | 1 => valS451 b
  | 2 => valS452 c
  | 3 => valS453 d
  | 4 => valS454 e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS45_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS45 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valS450 a
  | 0, 1 => valS451 b
  | 0, 2 => pES452 (valS451 b)
  | 0, 3 => pES454 (valS451 b)
  | 0, 4 => valS452 c
  | 1, 0 => pES456 (valS451 b)
  | 1, 1 => pES456 (valS450 a)
  | 1, 2 => pES458 (valS451 b)
  | 1, 3 => pES4510 (valS451 b)
  | 1, 4 => pES456 (valS452 c)
  | 2, 0 => pES4512 (valS451 b)
  | 2, 1 => pES4514 (valS451 b)
  | 2, 2 => pES4512 (valS450 a)
  | 2, 3 => pES4516 (valS451 b)
  | 2, 4 => pES4512 (valS452 c)
  | 3, 0 => pES4518 (valS451 b)
  | 3, 1 => pES4520 (valS451 b)
  | 3, 2 => pES4522 (valS451 b)
  | 3, 3 => pES4518 (valS450 a)
  | 3, 4 => pES4518 (valS452 c)
  | 4, 0 => valS453 d
  | 4, 1 => pES456 (valS453 d)
  | 4, 2 => pES4512 (valS453 d)
  | 4, 3 => pES4518 (valS453 d)
  | 4, 4 => valS454 e

theorem tabS45_eq_transport (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) :
    tabS45 a b c d e = Magma.transport permES45 trS45 (decS45 a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `22` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `24` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS45 : Fin 22 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabS45 0 0 0 0 0
  | 1 => tabS45 0 0 1 0 0
  | 2 => tabS45 0 0 1 1 0
  | 3 => tabS45 0 1 0 0 0
  | 4 => tabS45 0 1 0 1 0
  | 5 => tabS45 0 1 1 1 0
  | 6 => tabS45 0 2 0 0 0
  | 7 => tabS45 0 2 0 1 0
  | 8 => tabS45 0 2 1 0 0
  | 9 => tabS45 0 2 1 1 0
  | 10 => tabS45 1 0 0 0 0
  | 11 => tabS45 1 0 0 1 0
  | 12 => tabS45 1 0 1 0 0
  | 13 => tabS45 1 0 1 1 0
  | 14 => tabS45 1 1 0 0 0
  | 15 => tabS45 1 1 0 1 0
  | 16 => tabS45 1 1 1 0 0
  | 17 => tabS45 1 1 1 1 0
  | 18 => tabS45 1 2 0 0 0
  | 19 => tabS45 1 2 0 1 0
  | 20 => tabS45 1 2 1 0 0
  | _ => tabS45 1 2 1 1 0

/-- Which of the `22` members a given invariant tuple is, so that `mem_of_isExactS45` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS45 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

/-- The arguments as one mixed-radix index, which is how `rankArrS45` is addressed. -/
def encTS45 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Nat :=
  a.1 * 12 +
    b.1 * 4 +
    c.1 * 2 +
    d.1 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS45 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Fin 22 :=
  ⟨min (rankArrS45.getD (encTS45 a b c d e) 0) 21, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS45 (i : Fin 22) : Magma (Fin 5) := Magma.mk (memS45 i)

theorem exactS45_isEndo (i : Fin 22) (j : Fin 24) : (exactS45 i).IsEndo ⇑(eES45 j) := by
  simp only [eES45, coe_permOf]; revert i j; native_decide

theorem exactS45_not_isEndo (i : Fin 22) (j : Fin 1) : ¬ (exactS45 i).IsEndo ⇑(eXS45 j) := by
  simp only [eXS45, coe_permOf]; revert i j; native_decide

/-- `rankS45` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS45` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS45 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1)
    (h : Magma.isExact (tabS45 a b c d e) permES45 permXS45 = true) :
    memS45 (rankS45 a b c d e) = tabS45 a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `22` listed
members. -/
theorem mem_of_isExactS45 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1)
    (h : Magma.isExact (tabS45 a b c d e) permES45 permXS45 = true) :
    ∃ i, memS45 i = tabS45 a b c d e :=
  ⟨_, mem_rankS45 a b c d e h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS45`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS45` turns that into a member index. -/
theorem exists_exactS45 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eES45 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS45 i)) : ∃ i, exactS45 i = M := by
  simp only [eES45, coe_permOf] at hE
  simp only [eXS45, coe_permOf] at hX
  have hop : M.op = Magma.transport permES45 trS45 (fun i ↦ M.op (repS45 i).1 (repS45 i).2) :=
    Magma.op_eq_transport (rep := repS45) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES45) (idx := stabIdxS450) (a := (repS45 0).1) (b := (repS45 0).2)
    (val := valS450) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES45) (idx := stabIdxS451) (a := (repS45 1).1) (b := (repS45 1).2)
    (val := valS451) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES45) (idx := stabIdxS452) (a := (repS45 2).1) (b := (repS45 2).2)
    (val := valS452) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES45) (idx := stabIdxS453) (a := (repS45 3).1) (b := (repS45 3).2)
    (val := valS453) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES45) (idx := stabIdxS454) (a := (repS45 4).1) (b := (repS45 4).2)
    (val := valS454) hE (by decide) (by decide)
  have hdec : decS45 a b c d e = fun i ↦ M.op (repS45 i).1 (repS45 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tabS45 a b c d e = M.op := by
    rw [tabS45_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS45 a b c d e) permES45 permXS45 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS45 a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`24` group of `Magma.permES45`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS45 {L L' : Law.NatMagmaLaw} {i : Fin 22}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactS45 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactS45 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS45 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS45
    (fun k ↦ (Magma.exactS45_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS45_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
