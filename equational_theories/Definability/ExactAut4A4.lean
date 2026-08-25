import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `A4` on `Fin 4`

One class of `Definability/ExactAut4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`12` group `⟨(0 1)(2 3), (0 2)(1 3), (1 2 3)⟩` -/

/-- The `12` elements of the group: `()`, `(1 2 3)`, `(1 3 2)`, `(0 1)(2 3)`, `(0 1 2)`, `(0 1 3)`,
`(0 2 1)`, `(0 2 3)`, `(0 2)(1 3)`, `(0 3 1)`, `(0 3 2)`, `(0 3)(1 2)`. -/
def pEA40 : Fin 4 → Fin 4 := id
def pEA41 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1
def pEA42 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2
def pEA43 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
def pEA44 : Fin 4 → Fin 4 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3
def pEA45 : Fin 4 → Fin 4 | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0
def pEA46 : Fin 4 → Fin 4 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3
def pEA47 : Fin 4 → Fin 4 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0
def pEA48 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pEA49 : Fin 4 → Fin 4 | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1
def pEA410 : Fin 4 → Fin 4 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2
def pEA411 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permEA4 : Fin 12 → Fin 4 → Fin 4
  | 0 => pEA40
  | 1 => pEA41
  | 2 => pEA42
  | 3 => pEA43
  | 4 => pEA44
  | 5 => pEA45
  | 6 => pEA46
  | 7 => pEA47
  | 8 => pEA48
  | 9 => pEA49
  | 10 => pEA410
  | 11 => pEA411

def permEinvA4 : Fin 12 → Fin 4 → Fin 4
  | 0 => pEA40
  | 1 => pEA42
  | 2 => pEA41
  | 3 => pEA43
  | 4 => pEA46
  | 5 => pEA49
  | 6 => pEA44
  | 7 => pEA410
  | 8 => pEA48
  | 9 => pEA45
  | 10 => pEA47
  | 11 => pEA411

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEA4 (i : Fin 12) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permEA4 i) (permEinvA4 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(1 2)`. Every subgroup properly containing
the group above contains it, so a magma admitting the group and not this has that group as its
automorphism group exactly. -/
def pXA40 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pXA40inv : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3

def permXA4 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXA40

def permXinvA4 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXA40inv

def eXA4 (i : Fin 1) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permXA4 i) (permXinvA4 i) (by revert i; decide)

/-- One representative per orbit of the group on the `16` cells; there are `2`, so an invariant
operation is `2` values. -/
def repA4 : Fin 2 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trA4 : Fin 4 → Fin 4 → Fin 2 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 1, 0 => (1, 3)
  | 1, 1 => (0, 3)
  | 1, 2 => (1, 4)
  | 1, 3 => (1, 5)
  | 2, 0 => (1, 6)
  | 2, 1 => (1, 7)
  | 2, 2 => (0, 6)
  | 2, 3 => (1, 8)
  | 3, 0 => (1, 9)
  | 3, 1 => (1, 10)
  | 3, 2 => (1, 11)
  | 3, 3 => (0, 9)

/-- The `3` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxA40 : Fin 3 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valA40 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxA41 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` orbit values named by the family's arguments. -/
def decA4 (a : Fin 1) (b : Fin 4) : Fin 2 → Fin 4
  | 0 => valA40 a
  | 1 => b

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabA4_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabA4 (a : Fin 1) (b : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => valA40 a
  | 0, 1 => b
  | 0, 2 => pEA41 b
  | 0, 3 => pEA42 b
  | 1, 0 => pEA43 b
  | 1, 1 => pEA43 (valA40 a)
  | 1, 2 => pEA44 b
  | 1, 3 => pEA45 b
  | 2, 0 => pEA46 b
  | 2, 1 => pEA47 b
  | 2, 2 => pEA46 (valA40 a)
  | 2, 3 => pEA48 b
  | 3, 0 => pEA49 b
  | 3, 1 => pEA410 b
  | 3, 2 => pEA411 b
  | 3, 3 => pEA49 (valA40 a)

theorem tabA4_eq_transport (a : Fin 1) (b : Fin 4) :
    tabA4 a b = Magma.transport permEA4 trA4 (decA4 a b) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 4` whose automorphism group is exactly this group, listed under one
index. Of the `4` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memA4 : Fin 2 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabA4 0 2
  | 1 => tabA4 0 3

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExactA4` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrA4 : Array Nat := #[
  0, 0, 0, 1]

/-- The arguments as one mixed-radix index, which is how `rankArrA4` is addressed. -/
def encTA4 (a : Fin 1) (b : Fin 4) : Nat :=
  a.1 * 4 +
    b.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankA4 (a : Fin 1) (b : Fin 4) : Fin 2 :=
  ⟨min (rankArrA4.getD (encTA4 a b) 0) 1, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactA4 (i : Fin 2) : Magma (Fin 4) := Magma.mk (memA4 i)

theorem exactA4_isEndo (i : Fin 2) (j : Fin 12) : (exactA4 i).IsEndo ⇑(eEA4 j) := by
  simp only [eEA4, coe_permOf]; revert i j; native_decide

theorem exactA4_not_isEndo (i : Fin 2) (j : Fin 1) : ¬ (exactA4 i).IsEndo ⇑(eXA4 j) := by
  simp only [eXA4, coe_permOf]; revert i j; native_decide

/-- `rankA4` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memA4` for the index would be a comparison per tuple and
member. -/
theorem mem_rankA4 (a : Fin 1) (b : Fin 4)
    (h : Magma.isExact (tabA4 a b) permEA4 permXA4 = true) :
    memA4 (rankA4 a b) = tabA4 a b := by
  revert h; revert a b; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `2` listed
members. -/
theorem mem_of_isExactA4 (a : Fin 1) (b : Fin 4)
    (h : Magma.isExact (tabA4 a b) permEA4 permXA4 = true) :
    ∃ i, memA4 i = tabA4 a b :=
  ⟨_, mem_rankA4 a b h⟩

/-- A magma on `Fin 4` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactA4`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactA4` turns that into a member index. -/
theorem exists_exactA4 {M : Magma (Fin 4)} (hE : ∀ i, M.IsEndo ⇑(eEA4 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXA4 i)) : ∃ i, exactA4 i = M := by
  simp only [eEA4, coe_permOf] at hE
  simp only [eXA4, coe_permOf] at hX
  have hop : M.op = Magma.transport permEA4 trA4 (fun i ↦ M.op (repA4 i).1 (repA4 i).2) :=
    Magma.op_eq_transport (rep := repA4) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEA4) (idx := stabIdxA40) (a := (repA4 0).1) (b := (repA4 0).2)
    (val := valA40) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEA4) (idx := stabIdxA41) (a := (repA4 1).1) (b := (repA4 1).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decA4 a b = fun i ↦ M.op (repA4 i).1 (repA4 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
  have key : tabA4 a b = M.op := by
    rw [tabA4_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabA4 a b) permEA4 permXA4 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactA4 a b hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose automorphism
group is exactly the order-`12` group of `Magma.permEA4`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactA4 {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 4) (Magma.exactA4 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.exactA4 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactA4 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactA4
    (fun k ↦ (Magma.exactA4_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactA4_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
