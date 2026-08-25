import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `D4` on `Fin 4`

One class of `Definability/ExactAut4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`8` group `⟨(0 1)(2 3), (0 2)(1 3), (0 2 1 3)⟩` -/

/-- The `8` elements of the group: `()`, `(2 3)`, `(0 1)`, `(0 1)(2 3)`, `(0 2)(1 3)`, `(0 2 1 3)`,
`(0 3 1 2)`, `(0 3)(1 2)`. -/
def pED40 : Fin 4 → Fin 4 := id
def pED41 : Fin 4 → Fin 4 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2
def pED42 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3
def pED43 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
def pED44 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pED45 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0
def pED46 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1
def pED47 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permED4 : Fin 8 → Fin 4 → Fin 4
  | 0 => pED40
  | 1 => pED41
  | 2 => pED42
  | 3 => pED43
  | 4 => pED44
  | 5 => pED45
  | 6 => pED46
  | 7 => pED47

def permEinvD4 : Fin 8 → Fin 4 → Fin 4
  | 0 => pED40
  | 1 => pED41
  | 2 => pED42
  | 3 => pED43
  | 4 => pED44
  | 5 => pED46
  | 6 => pED45
  | 7 => pED47

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eED4 (i : Fin 8) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permED4 i) (permEinvD4 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(1 2)`. Every subgroup properly containing
the group above contains it, so a magma admitting the group and not this has that group as its
automorphism group exactly. -/
def pXD40 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pXD40inv : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3

def permXD4 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXD40

def permXinvD4 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXD40inv

def eXD4 (i : Fin 1) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permXD4 i) (permXinvD4 i) (by revert i; decide)

/-- One representative per orbit of the group on the `16` cells; there are `3`, so an invariant
operation is `3` values. -/
def repD4 : Fin 3 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trD4 : Fin 4 → Fin 4 → Fin 3 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (2, 2)
  | 1, 3 => (2, 3)
  | 2, 0 => (2, 4)
  | 2, 1 => (2, 5)
  | 2, 2 => (0, 4)
  | 2, 3 => (1, 4)
  | 3, 0 => (2, 6)
  | 3, 1 => (2, 7)
  | 3, 2 => (1, 6)
  | 3, 3 => (0, 6)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD40 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def valD40 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxD41 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def valD41 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxD42 : Fin 1 → Fin 8
  | 0 => 0

/-- The `3` orbit values named by the family's arguments. -/
def decD4 (a b : Fin 2) (c : Fin 4) : Fin 3 → Fin 4
  | 0 => valD40 a
  | 1 => valD41 b
  | 2 => c

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabD4_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabD4 (a b : Fin 2) (c : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => valD40 a
  | 0, 1 => valD41 b
  | 0, 2 => c
  | 0, 3 => pED41 c
  | 1, 0 => pED42 (valD41 b)
  | 1, 1 => pED42 (valD40 a)
  | 1, 2 => pED42 c
  | 1, 3 => pED43 c
  | 2, 0 => pED44 c
  | 2, 1 => pED45 c
  | 2, 2 => pED44 (valD40 a)
  | 2, 3 => pED44 (valD41 b)
  | 3, 0 => pED46 c
  | 3, 1 => pED47 c
  | 3, 2 => pED46 (valD41 b)
  | 3, 3 => pED46 (valD40 a)

theorem tabD4_eq_transport (a b : Fin 2) (c : Fin 4) :
    tabD4 a b c = Magma.transport permED4 trD4 (decD4 a b c) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `14` magmas on `Fin 4` whose automorphism group is exactly this group, listed under one
index. Of the `16` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memD4 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabD4 0 0 1
  | 1 => tabD4 0 0 2
  | 2 => tabD4 0 0 3
  | 3 => tabD4 0 1 0
  | 4 => tabD4 0 1 1
  | 5 => tabD4 0 1 3
  | 6 => tabD4 1 0 0
  | 7 => tabD4 1 0 1
  | 8 => tabD4 1 0 2
  | 9 => tabD4 1 0 3
  | 10 => tabD4 1 1 0
  | 11 => tabD4 1 1 1
  | 12 => tabD4 1 1 2
  | 13 => tabD4 1 1 3

/-- Which of the `14` members a given invariant tuple is, so that `mem_of_isExactD4` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrD4 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- The arguments as one mixed-radix index, which is how `rankArrD4` is addressed. -/
def encTD4 (a b : Fin 2) (c : Fin 4) : Nat :=
  a.1 * 8 +
    b.1 * 4 +
    c.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankD4 (a b : Fin 2) (c : Fin 4) : Fin 14 :=
  ⟨min (rankArrD4.getD (encTD4 a b c) 0) 13, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactD4 (i : Fin 14) : Magma (Fin 4) := Magma.mk (memD4 i)

theorem exactD4_isEndo (i : Fin 14) (j : Fin 8) : (exactD4 i).IsEndo ⇑(eED4 j) := by
  simp only [eED4, coe_permOf]; revert i j; native_decide

theorem exactD4_not_isEndo (i : Fin 14) (j : Fin 1) : ¬ (exactD4 i).IsEndo ⇑(eXD4 j) := by
  simp only [eXD4, coe_permOf]; revert i j; native_decide

/-- `rankD4` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memD4` for the index would be a comparison per tuple and
member. -/
theorem mem_rankD4 (a b : Fin 2) (c : Fin 4)
    (h : Magma.isExact (tabD4 a b c) permED4 permXD4 = true) :
    memD4 (rankD4 a b c) = tabD4 a b c := by
  revert h; revert a b c; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `14` listed
members. -/
theorem mem_of_isExactD4 (a b : Fin 2) (c : Fin 4)
    (h : Magma.isExact (tabD4 a b c) permED4 permXD4 = true) :
    ∃ i, memD4 i = tabD4 a b c :=
  ⟨_, mem_rankD4 a b c h⟩

/-- A magma on `Fin 4` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactD4`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactD4` turns that into a member index. -/
theorem exists_exactD4 {M : Magma (Fin 4)} (hE : ∀ i, M.IsEndo ⇑(eED4 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXD4 i)) : ∃ i, exactD4 i = M := by
  simp only [eED4, coe_permOf] at hE
  simp only [eXD4, coe_permOf] at hX
  have hop : M.op = Magma.transport permED4 trD4 (fun i ↦ M.op (repD4 i).1 (repD4 i).2) :=
    Magma.op_eq_transport (rep := repD4) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permED4) (idx := stabIdxD40) (a := (repD4 0).1) (b := (repD4 0).2)
    (val := valD40) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permED4) (idx := stabIdxD41) (a := (repD4 1).1) (b := (repD4 1).2)
    (val := valD41) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permED4) (idx := stabIdxD42) (a := (repD4 2).1) (b := (repD4 2).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decD4 a b c = fun i ↦ M.op (repD4 i).1 (repD4 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have key : tabD4 a b c = M.op := by
    rw [tabD4_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabD4 a b c) permED4 permXD4 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactD4 a b c hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose automorphism
group is exactly the order-`8` group of `Magma.permED4`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactD4 {L L' : Law.NatMagmaLaw} {i : Fin 14}
    (hsrc : @satisfies _ (Fin 4) (Magma.exactD4 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.exactD4 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactD4 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactD4
    (fun k ↦ (Magma.exactD4_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactD4_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
