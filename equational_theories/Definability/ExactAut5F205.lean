import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `F205` on `Fin 5`

One class of `Definability/ExactAut5.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`20` group `⟨(0 1 2 4 3), (1 2 3 4)⟩` -/

/-- The `20` elements of the group: `()`, `(1 2 3 4)`, `(1 3)(2 4)`, `(1 4 3 2)`, `(0 1)(2 3)`, `(0
1 2 4 3)`, `(0 1 3 4)`, `(0 1 4 2)`, `(0 2 4 1)`, `(0 2)(3 4)`, `(0 2 1 3)`, `(0 2 3 1 4)`, `(0 3 4
2 1)`, `(0 3 2 4)`, `(0 3 1 2)`, `(0 3)(1 4)`, `(0 4 3 1)`, `(0 4 2 3)`, `(0 4)(1 2)`, `(0 4 1 3
2)`. -/
def pEF2050 : Fin 5 → Fin 5 := id
def pEF2051 : Fin 5 → Fin 5 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1
def pEF2052 : Fin 5 → Fin 5 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2
def pEF2053 : Fin 5 → Fin 5 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3
def pEF2054 : Fin 5 → Fin 5 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4
def pEF2055 : Fin 5 → Fin 5 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3
def pEF2056 : Fin 5 → Fin 5 | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0
def pEF2057 : Fin 5 → Fin 5 | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2
def pEF2058 : Fin 5 → Fin 5 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1
def pEF2059 : Fin 5 → Fin 5 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3
def pEF20510 : Fin 5 → Fin 5 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4
def pEF20511 : Fin 5 → Fin 5 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0
def pEF20512 : Fin 5 → Fin 5 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2
def pEF20513 : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0
def pEF20514 : Fin 5 → Fin 5 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4
def pEF20515 : Fin 5 → Fin 5 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1
def pEF20516 : Fin 5 → Fin 5 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3
def pEF20517 : Fin 5 → Fin 5 | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2
def pEF20518 : Fin 5 → Fin 5 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0
def pEF20519 : Fin 5 → Fin 5 | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1

def permEF205 : Fin 20 → Fin 5 → Fin 5
  | 0 => pEF2050
  | 1 => pEF2051
  | 2 => pEF2052
  | 3 => pEF2053
  | 4 => pEF2054
  | 5 => pEF2055
  | 6 => pEF2056
  | 7 => pEF2057
  | 8 => pEF2058
  | 9 => pEF2059
  | 10 => pEF20510
  | 11 => pEF20511
  | 12 => pEF20512
  | 13 => pEF20513
  | 14 => pEF20514
  | 15 => pEF20515
  | 16 => pEF20516
  | 17 => pEF20517
  | 18 => pEF20518
  | _ => pEF20519

def permEinvF205 : Fin 20 → Fin 5 → Fin 5
  | 0 => pEF2050
  | 1 => pEF2053
  | 2 => pEF2052
  | 3 => pEF2051
  | 4 => pEF2054
  | 5 => pEF20512
  | 6 => pEF20516
  | 7 => pEF2058
  | 8 => pEF2057
  | 9 => pEF2059
  | 10 => pEF20514
  | 11 => pEF20519
  | 12 => pEF2055
  | 13 => pEF20517
  | 14 => pEF20510
  | 15 => pEF20515
  | 16 => pEF2056
  | 17 => pEF20513
  | 18 => pEF20518
  | _ => pEF20511

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEF205 (i : Fin 20) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permEF205 i) (permEinvF205 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3)`. Every subgroup properly containing
the group above contains it, so a magma admitting the group and not this has that group as its
automorphism group exactly. -/
def pXF2050 : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4
def pXF2050inv : Fin 5 → Fin 5 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4

def permXF205 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXF2050

def permXinvF205 : Fin 1 → Fin 5 → Fin 5
  | 0 => pXF2050inv

def eXF205 (i : Fin 1) : Equiv.Perm (Fin 5) :=
  Magma.permOf (permXF205 i) (permXinvF205 i) (by revert i; decide)

/-- One representative per orbit of the group on the `25` cells; there are `2`, so an invariant
operation is `2` values. -/
def repF205 : Fin 2 → Fin 5 × Fin 5
  | 0 => (0, 0)
  | 1 => (0, 1)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trF205 : Fin 5 → Fin 5 → Fin 2 × Fin 20
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 0, 4 => (1, 3)
  | 1, 0 => (1, 4)
  | 1, 1 => (0, 4)
  | 1, 2 => (1, 5)
  | 1, 3 => (1, 6)
  | 1, 4 => (1, 7)
  | 2, 0 => (1, 8)
  | 2, 1 => (1, 9)
  | 2, 2 => (0, 8)
  | 2, 3 => (1, 10)
  | 2, 4 => (1, 11)
  | 3, 0 => (1, 12)
  | 3, 1 => (1, 13)
  | 3, 2 => (1, 14)
  | 3, 3 => (0, 12)
  | 3, 4 => (1, 15)
  | 4, 0 => (1, 16)
  | 4, 1 => (1, 17)
  | 4, 2 => (1, 18)
  | 4, 3 => (1, 19)
  | 4, 4 => (0, 16)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxF2050 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valF2050 : Fin 1 → Fin 5
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 5`. -/
def stabIdxF2051 : Fin 1 → Fin 20
  | 0 => 0

/-- The `2` orbit values named by the family's arguments. -/
def decF205 (a : Fin 1) (b : Fin 5) : Fin 2 → Fin 5
  | 0 => valF2050 a
  | 1 => b

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabF205_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabF205 (a : Fin 1) (b : Fin 5) : Fin 5 → Fin 5 → Fin 5
  | 0, 0 => valF2050 a
  | 0, 1 => b
  | 0, 2 => pEF2051 b
  | 0, 3 => pEF2052 b
  | 0, 4 => pEF2053 b
  | 1, 0 => pEF2054 b
  | 1, 1 => pEF2054 (valF2050 a)
  | 1, 2 => pEF2055 b
  | 1, 3 => pEF2056 b
  | 1, 4 => pEF2057 b
  | 2, 0 => pEF2058 b
  | 2, 1 => pEF2059 b
  | 2, 2 => pEF2058 (valF2050 a)
  | 2, 3 => pEF20510 b
  | 2, 4 => pEF20511 b
  | 3, 0 => pEF20512 b
  | 3, 1 => pEF20513 b
  | 3, 2 => pEF20514 b
  | 3, 3 => pEF20512 (valF2050 a)
  | 3, 4 => pEF20515 b
  | 4, 0 => pEF20516 b
  | 4, 1 => pEF20517 b
  | 4, 2 => pEF20518 b
  | 4, 3 => pEF20519 b
  | 4, 4 => pEF20516 (valF2050 a)

theorem tabF205_eq_transport (a : Fin 1) (b : Fin 5) :
    tabF205 a b = Magma.transport permEF205 trF205 (decF205 a b) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `3` magmas on `Fin 5` whose automorphism group is exactly this group, listed under one
index. Of the `5` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memF205 : Fin 3 → Fin 5 → Fin 5 → Fin 5
  | 0 => tabF205 0 2
  | 1 => tabF205 0 3
  | 2 => tabF205 0 4

/-- Which of the `3` members a given invariant tuple is, so that `mem_of_isExactF205` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrF205 : Array Nat := #[
  0, 0, 0, 1, 2]

/-- The arguments as one mixed-radix index, which is how `rankArrF205` is addressed. -/
def encTF205 (a : Fin 1) (b : Fin 5) : Nat :=
  a.1 * 5 +
    b.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankF205 (a : Fin 1) (b : Fin 5) : Fin 3 :=
  ⟨min (rankArrF205.getD (encTF205 a b) 0) 2, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactF205 (i : Fin 3) : Magma (Fin 5) := Magma.mk (memF205 i)

theorem exactF205_isEndo (i : Fin 3) (j : Fin 20) : (exactF205 i).IsEndo ⇑(eEF205 j) := by
  simp only [eEF205, coe_permOf]; revert i j; native_decide

theorem exactF205_not_isEndo (i : Fin 3) (j : Fin 1) : ¬ (exactF205 i).IsEndo ⇑(eXF205 j) := by
  simp only [eXF205, coe_permOf]; revert i j; native_decide

/-- `rankF205` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memF205` for the index would be a comparison per tuple and
member. -/
theorem mem_rankF205 (a : Fin 1) (b : Fin 5)
    (h : Magma.isExact (tabF205 a b) permEF205 permXF205 = true) :
    memF205 (rankF205 a b) = tabF205 a b := by
  revert h; revert a b; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `3` listed
members. -/
theorem mem_of_isExactF205 (a : Fin 1) (b : Fin 5)
    (h : Magma.isExact (tabF205 a b) permEF205 permXF205 = true) :
    ∃ i, memF205 i = tabF205 a b :=
  ⟨_, mem_rankF205 a b h⟩

/-- A magma on `Fin 5` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactF205`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactF205` turns that into a member index. -/
theorem exists_exactF205 {M : Magma (Fin 5)} (hE : ∀ i, M.IsEndo ⇑(eEF205 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXF205 i)) : ∃ i, exactF205 i = M := by
  simp only [eEF205, coe_permOf] at hE
  simp only [eXF205, coe_permOf] at hX
  have hop : M.op = Magma.transport permEF205 trF205 (fun i ↦ M.op (repF205 i).1 (repF205 i).2) :=
    Magma.op_eq_transport (rep := repF205) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEF205) (idx := stabIdxF2050) (a := (repF205 0).1) (b := (repF205 0).2)
    (val := valF2050) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEF205) (idx := stabIdxF2051) (a := (repF205 1).1) (b := (repF205 1).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decF205 a b = fun i ↦ M.op (repF205 i).1 (repF205 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
  have key : tabF205 a b = M.op := by
    rw [tabF205_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabF205 a b) permEF205 permXF205 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactF205 a b hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 5`.** If `L'` has a model on `Fin 5` whose automorphism
group is exactly the order-`20` group of `Magma.permEF205`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactF205 {L L' : Law.NatMagmaLaw} {i : Fin 3}
    (hsrc : @satisfies _ (Fin 5) (Magma.exactF205 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 5) (Magma.exactF205 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactF205 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactF205
    (fun k ↦ (Magma.exactF205_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactF205_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
