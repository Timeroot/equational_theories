import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `A45` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`12` group `⟨(1 2)(3 4), (1 3)(2 4), (2 3 4)⟩` -/

/-- The `12` elements of the group: `()`, `(2 3 4)`, `(2 4 3)`, `(1 2)(3 4)`, `(1 2 3)`, `(1 2 4)`,
`(1 3 2)`, `(1 3 4)`, `(1 3)(2 4)`, `(1 4 2)`, `(1 4 3)`, `(1 4)(2 3)`. -/
def pEA450 : Fin 5 → Fin 5 := id
def pEA451 : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2
def pEA452 : Fin 5 → Fin 5 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3
def pEA453 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3
def pEA454 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4
def pEA455 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1
def pEA456 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4
def pEA457 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1
def pEA458 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2
def pEA459 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2
def pEA4510 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3
def pEA4511 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1

def permEA45 : Fin 12 → Fin 5 → Fin 5
  | 0 => pEA450
  | 1 => pEA451
  | 2 => pEA452
  | 3 => pEA453
  | 4 => pEA454
  | 5 => pEA455
  | 6 => pEA456
  | 7 => pEA457
  | 8 => pEA458
  | 9 => pEA459
  | 10 => pEA4510
  | 11 => pEA4511

def permEinvA45 : Fin 12 → Fin 5 → Fin 5
  | 0 => pEA450
  | 1 => pEA452
  | 2 => pEA451
  | 3 => pEA453
  | 4 => pEA456
  | 5 => pEA459
  | 6 => pEA454
  | 7 => pEA4510
  | 8 => pEA458
  | 9 => pEA455
  | 10 => pEA457
  | 11 => pEA4511

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEA45 (i : Fin 12) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permEA45 i) (permEinvA45 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(1 2 3 4)`, `(0 2 4 3 1)`. Every
subgroup properly containing the group above contains one of them, so a magma admitting the group
and not these has that group as its automorphism group exactly. -/
def pXA450 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1
def pXA451 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 3
def pXA450inv : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3
def pXA451inv : Fin 5 → Fin 5 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 2

def permXA45 : Fin 2 → Fin 5 → Fin 5
  | 0 => pXA450
  | 1 => pXA451

def permXinvA45 : Fin 2 → Fin 5 → Fin 5
  | 0 => pXA450inv
  | 1 => pXA451inv

def eXA45 (i : Fin 2) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXA45 i) (permXinvA45 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `5`, so an invariant
operation is `5` values. -/
def repA45 : Fin 5 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trA45 : Fin 5 → Fin 5 → Fin 5 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 3)
  | 0, 3 => (1, 6)
  | 0, 4 => (1, 9)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (4, 1)
  | 1, 4 => (4, 2)
  | 2, 0 => (2, 3)
  | 2, 1 => (4, 3)
  | 2, 2 => (3, 3)
  | 2, 3 => (4, 4)
  | 2, 4 => (4, 5)
  | 3, 0 => (2, 6)
  | 3, 1 => (4, 6)
  | 3, 2 => (4, 7)
  | 3, 3 => (3, 6)
  | 3, 4 => (4, 8)
  | 4, 0 => (2, 9)
  | 4, 1 => (4, 9)
  | 4, 2 => (4, 10)
  | 4, 3 => (4, 11)
  | 4, 4 => (3, 9)

/-- The `12` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxA450 : Fin 12 → Fin 12
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
def valA450 : Fin 1 → Fin 5
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxA451 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valA451 : Fin 2 → Fin 5
  | 0 => 0
  | 1 => 1

/-- The `3` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxA452 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valA452 : Fin 2 → Fin 5
  | 0 => 0
  | 1 => 1

/-- The `3` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxA453 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valA453 : Fin 2 → Fin 5
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxA454 : Fin 1 → Fin 12
  | 0 => 0

/-- The `5` orbit values named by the family's arguments. -/
def decA45 (a : Fin 1) (b c d : Fin 2) (e : Fin 5) : Fin 5 → Fin 5
  | 0 => valA450 a
  | 1 => valA451 b
  | 2 => valA452 c
  | 3 => valA453 d
  | 4 => e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabA45_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabA45 (a : Fin 1) (b c d : Fin 2) (e : Fin 5) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valA450 a
  | 0, 1 => valA451 b
  | 0, 2 => pEA453 (valA451 b)
  | 0, 3 => pEA456 (valA451 b)
  | 0, 4 => pEA459 (valA451 b)
  | 1, 0 => valA452 c
  | 1, 1 => valA453 d
  | 1, 2 => e
  | 1, 3 => pEA451 e
  | 1, 4 => pEA452 e
  | 2, 0 => pEA453 (valA452 c)
  | 2, 1 => pEA453 e
  | 2, 2 => pEA453 (valA453 d)
  | 2, 3 => pEA454 e
  | 2, 4 => pEA455 e
  | 3, 0 => pEA456 (valA452 c)
  | 3, 1 => pEA456 e
  | 3, 2 => pEA457 e
  | 3, 3 => pEA456 (valA453 d)
  | 3, 4 => pEA458 e
  | 4, 0 => pEA459 (valA452 c)
  | 4, 1 => pEA459 e
  | 4, 2 => pEA4510 e
  | 4, 3 => pEA4511 e
  | 4, 4 => pEA459 (valA453 d)

theorem tabA45_eq_transport (a : Fin 1) (b c d : Fin 2) (e : Fin 5) :
    tabA45 a b c d e = Magma.transport permEA45 trA45 (decA45 a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `16` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `40` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memA45 : Fin 16 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabA45 0 0 0 0 3
  | 1 => tabA45 0 0 0 0 4
  | 2 => tabA45 0 0 0 1 3
  | 3 => tabA45 0 0 0 1 4
  | 4 => tabA45 0 0 1 0 3
  | 5 => tabA45 0 0 1 0 4
  | 6 => tabA45 0 0 1 1 3
  | 7 => tabA45 0 0 1 1 4
  | 8 => tabA45 0 1 0 0 3
  | 9 => tabA45 0 1 0 0 4
  | 10 => tabA45 0 1 0 1 3
  | 11 => tabA45 0 1 0 1 4
  | 12 => tabA45 0 1 1 0 3
  | 13 => tabA45 0 1 1 0 4
  | 14 => tabA45 0 1 1 1 3
  | _ => tabA45 0 1 1 1 4

/-- Which of the `16` members a given invariant tuple is, so that `mem_of_isExactA45` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrA45 : Array Nat := #[
  0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 0, 0, 0, 4, 5, 0, 0, 0, 6, 7, 0, 0, 0, 8, 9, 0, 0, 0, 10, 11, 0,
  0, 0, 12, 13, 0, 0, 0, 14, 15]

/-- The arguments as one mixed-radix index, which is how `rankArrA45` is addressed. -/
def encTA45 (a : Fin 1) (b c d : Fin 2) (e : Fin 5) : Nat :=
  a.1 * 40 +
    b.1 * 20 +
    c.1 * 10 +
    d.1 * 5 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankA45 (a : Fin 1) (b c d : Fin 2) (e : Fin 5) : Fin 16 :=
  ⟨min (rankArrA45.getD (encTA45 a b c d e) 0) 15, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactA45 (i : Fin 16) : Magma (Fin 5) := Magma.mk (memA45 i)

theorem exactA45_isEndo (i : Fin 16) (j : Fin 12) : (exactA45 i).IsEndo ⇑(eEA45 j) := by
  simp only [eEA45, coe_permOf]; revert i j; native_decide

theorem exactA45_not_isEndo (i : Fin 16) (j : Fin 2) : ¬ (exactA45 i).IsEndo ⇑(eXA45 j) := by
  simp only [eXA45, coe_permOf]; revert i j; native_decide

/-- `rankA45` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memA45` for the index would be a comparison per tuple and
member. -/
theorem mem_rankA45 (a : Fin 1) (b c d : Fin 2) (e : Fin 5)
    (h : Magma.isExact (tabA45 a b c d e) permEA45 permXA45 = true) :
    memA45 (rankA45 a b c d e) = tabA45 a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `16` listed
members. -/
theorem mem_of_isExactA45 (a : Fin 1) (b c d : Fin 2) (e : Fin 5)
    (h : Magma.isExact (tabA45 a b c d e) permEA45 permXA45 = true) :
    ∃ i, memA45 i = tabA45 a b c d e :=
  ⟨_, mem_rankA45 a b c d e h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactA45`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactA45` turns that into a member index. -/
theorem exists_exactA45 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eEA45 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXA45 i)) : ∃ i, exactA45 i = M := by
  simp only [eEA45, coe_permOf] at hE
  simp only [eXA45, coe_permOf] at hX
  have hop : M.op = Magma.transport permEA45 trA45 (fun i ↦ M.op (repA45 i).1 (repA45 i).2) :=
    Magma.op_eq_transport (rep := repA45) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEA45) (idx := stabIdxA450) (a := (repA45 0).1) (b := (repA45 0).2)
    (val := valA450) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEA45) (idx := stabIdxA451) (a := (repA45 1).1) (b := (repA45 1).2)
    (val := valA451) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEA45) (idx := stabIdxA452) (a := (repA45 2).1) (b := (repA45 2).2)
    (val := valA452) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEA45) (idx := stabIdxA453) (a := (repA45 3).1) (b := (repA45 3).2)
    (val := valA453) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEA45) (idx := stabIdxA454) (a := (repA45 4).1) (b := (repA45 4).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decA45 a b c d e = fun i ↦ M.op (repA45 i).1 (repA45 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tabA45 a b c d e = M.op := by
    rw [tabA45_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabA45 a b c d e) permEA45 permXA45 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactA45 a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`12` group of `Magma.permEA45`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactA45 {L L' : Law.NatMagmaLaw} {i : Fin 16}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactA45 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactA45 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactA45 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactA45
    (fun k ↦ (Magma.exactA45_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactA45_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
