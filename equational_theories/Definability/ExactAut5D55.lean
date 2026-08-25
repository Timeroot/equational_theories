import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D55` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`10` group `⟨(0 1 3 4 2), (1 2)(3 4)⟩` -/

/-- The `10` elements of the group: `()`, `(1 2)(3 4)`, `(0 1)(2 3)`, `(0 1 3 4 2)`, `(0 2 4 3 1)`,
`(0 2)(1 4)`, `(0 3)(2 4)`, `(0 3 2 1 4)`, `(0 4 1 2 3)`, `(0 4)(1 3)`. -/
def pED550 : Fin 5 → Fin 5 := id
def pED551 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3
def pED552 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4
def pED553 : Fin 5 → Fin 5 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 2
def pED554 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 3
def pED555 : Fin 5 → Fin 5 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 1
def pED556 : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2
def pED557 : Fin 5 → Fin 5 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0
def pED558 : Fin 5 → Fin 5 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1
def pED559 : Fin 5 → Fin 5 | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0

def permED55 : Fin 10 → Fin 5 → Fin 5
  | 0 => pED550
  | 1 => pED551
  | 2 => pED552
  | 3 => pED553
  | 4 => pED554
  | 5 => pED555
  | 6 => pED556
  | 7 => pED557
  | 8 => pED558
  | 9 => pED559

def permEinvD55 : Fin 10 → Fin 5 → Fin 5
  | 0 => pED550
  | 1 => pED551
  | 2 => pED552
  | 3 => pED554
  | 4 => pED553
  | 5 => pED555
  | 6 => pED556
  | 7 => pED558
  | 8 => pED557
  | 9 => pED559

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED55 (i : Fin 10) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permED55 i) (permEinvD55 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(0 4 3 2)`, `(0 4 2)`. Every subgroup
properly containing the group above contains one of them, so a magma admitting the group and not
these has that group as its automorphism group exactly. -/
def pXD550 : Fin 5 → Fin 5 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 3
def pXD551 : Fin 5 → Fin 5 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2
def pXD550inv : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 0
def pXD551inv : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0

def permXD55 : Fin 2 → Fin 5 → Fin 5
  | 0 => pXD550
  | 1 => pXD551

def permXinvD55 : Fin 2 → Fin 5 → Fin 5
  | 0 => pXD550inv
  | 1 => pXD551inv

def eXD55 (i : Fin 2) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXD55 i) (permXinvD55 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `3`, so an invariant
operation is `3` values. -/
def repD55 : Fin 3 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD55 : Fin 5 → Fin 5 → Fin 3 × Fin 10
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (2, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (2, 2)
  | 1, 3 => (1, 3)
  | 1, 4 => (2, 3)
  | 2, 0 => (1, 4)
  | 2, 1 => (2, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (2, 5)
  | 2, 4 => (1, 5)
  | 3, 0 => (2, 6)
  | 3, 1 => (1, 6)
  | 3, 2 => (2, 7)
  | 3, 3 => (0, 6)
  | 3, 4 => (1, 7)
  | 4, 0 => (2, 8)
  | 4, 1 => (2, 9)
  | 4, 2 => (1, 8)
  | 4, 3 => (1, 9)
  | 4, 4 => (0, 8)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxD550 : Fin 2 → Fin 10
  | 0 => 0
  | 1 => 1
def valD550 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxD551 : Fin 1 → Fin 10
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxD552 : Fin 1 → Fin 10
  | 0 => 0

/-- The `3` orbit values named by the family's arguments. -/
def decD55 (a : Fin 1) (b c : Fin 5) : Fin 3 → Fin 5
  | 0 => valD550 a
  | 1 => b
  | 2 => c

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD55_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD55 (a : Fin 1) (b c : Fin 5) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valD550 a
  | 0, 1 => b
  | 0, 2 => pED551 b
  | 0, 3 => c
  | 0, 4 => pED551 c
  | 1, 0 => pED552 b
  | 1, 1 => pED552 (valD550 a)
  | 1, 2 => pED552 c
  | 1, 3 => pED553 b
  | 1, 4 => pED553 c
  | 2, 0 => pED554 b
  | 2, 1 => pED554 c
  | 2, 2 => pED554 (valD550 a)
  | 2, 3 => pED555 c
  | 2, 4 => pED555 b
  | 3, 0 => pED556 c
  | 3, 1 => pED556 b
  | 3, 2 => pED557 c
  | 3, 3 => pED556 (valD550 a)
  | 3, 4 => pED557 b
  | 4, 0 => pED558 c
  | 4, 1 => pED559 c
  | 4, 2 => pED558 b
  | 4, 3 => pED559 b
  | 4, 4 => pED558 (valD550 a)

theorem tabD55_eq_transport (a : Fin 1) (b c : Fin 5) :
    tabD55 a b c = Magma.transport permED55 trD55 (decD55 a b c) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `20` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `25` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memD55 : Fin 20 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabD55 0 0 1
  | 1 => tabD55 0 0 2
  | 2 => tabD55 0 0 3
  | 3 => tabD55 0 0 4
  | 4 => tabD55 0 1 0
  | 5 => tabD55 0 1 1
  | 6 => tabD55 0 1 2
  | 7 => tabD55 0 1 4
  | 8 => tabD55 0 2 0
  | 9 => tabD55 0 2 1
  | 10 => tabD55 0 2 2
  | 11 => tabD55 0 2 3
  | 12 => tabD55 0 3 0
  | 13 => tabD55 0 3 1
  | 14 => tabD55 0 3 3
  | 15 => tabD55 0 3 4
  | 16 => tabD55 0 4 0
  | 17 => tabD55 0 4 2
  | 18 => tabD55 0 4 3
  | _ => tabD55 0 4 4

/-- Which of the `20` members a given invariant tuple is, so that `mem_of_isExactD55` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD55 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 10, 11, 0, 12, 13, 0, 14, 15, 16, 0, 17, 18, 19]

/-- The arguments as one mixed-radix index, which is how `rankArrD55` is addressed. -/
def encTD55 (a : Fin 1) (b c : Fin 5) : Nat :=
  a.1 * 25 +
    b.1 * 5 +
    c.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD55 (a : Fin 1) (b c : Fin 5) : Fin 20 :=
  ⟨min (rankArrD55.getD (encTD55 a b c) 0) 19, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD55 (i : Fin 20) : Magma (Fin 5) := Magma.mk (memD55 i)

theorem exactD55_isEndo (i : Fin 20) (j : Fin 10) : (exactD55 i).IsEndo ⇑(eED55 j) := by
  simp only [eED55, coe_permOf]; revert i j; native_decide

theorem exactD55_not_isEndo (i : Fin 20) (j : Fin 2) : ¬ (exactD55 i).IsEndo ⇑(eXD55 j) := by
  simp only [eXD55, coe_permOf]; revert i j; native_decide

/-- `rankD55` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD55` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD55 (a : Fin 1) (b c : Fin 5)
    (h : Magma.isExact (tabD55 a b c) permED55 permXD55 = true) :
    memD55 (rankD55 a b c) = tabD55 a b c := by
  revert h; revert a b c; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `20` listed
members. -/
theorem mem_of_isExactD55 (a : Fin 1) (b c : Fin 5)
    (h : Magma.isExact (tabD55 a b c) permED55 permXD55 = true) :
    ∃ i, memD55 i = tabD55 a b c :=
  ⟨_, mem_rankD55 a b c h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD55`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD55` turns that into a member index. -/
theorem exists_exactD55 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eED55 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD55 i)) : ∃ i, exactD55 i = M := by
  simp only [eED55, coe_permOf] at hE
  simp only [eXD55, coe_permOf] at hX
  have hop : M.op = Magma.transport permED55 trD55 (fun i ↦ M.op (repD55 i).1 (repD55 i).2) :=
    Magma.op_eq_transport (rep := repD55) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED55) (idx := stabIdxD550) (a := (repD55 0).1) (b := (repD55 0).2)
    (val := valD550) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED55) (idx := stabIdxD551) (a := (repD55 1).1) (b := (repD55 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED55) (idx := stabIdxD552) (a := (repD55 2).1) (b := (repD55 2).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decD55 a b c = fun i ↦ M.op (repD55 i).1 (repD55 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have key : tabD55 a b c = M.op := by
    rw [tabD55_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD55 a b c) permED55 permXD55 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD55 a b c hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`10` group of `Magma.permED55`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD55 {L L' : Law.NatMagmaLaw} {i : Fin 20}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactD55 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactD55 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD55 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD55
    (fun k ↦ (Magma.exactD55_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD55_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
