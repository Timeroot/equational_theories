import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S4b6` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 1)(2 3)(4 5), (0 1)(2 5)(3 4), (0 2)(1 4)(3 5)⟩` -/

/-- The `24` elements of the group: `()`, `(2 3 4 5)`, `(2 4)(3 5)`, `(2 5 4 3)`, `(0 1)(3 5)`, `(0
1)(2 3)(4 5)`, `(0 1)(2 4)`, `(0 1)(2 5)(3 4)`, `(0 2)(1 4)(3 5)`, `(0 2 1 4)`, `(0 2 3)(1 4 5)`,
`(0 2 5)(1 4 3)`, `(0 3 2)(1 5 4)`, `(0 3 4)(1 5 2)`, `(0 3 1 5)`, `(0 3)(1 5)(2 4)`, `(0 4 1 2)`,
`(0 4)(1 2)(3 5)`, `(0 4 5)(1 2 3)`, `(0 4 3)(1 2 5)`, `(0 5 2)(1 3 4)`, `(0 5 4)(1 3 2)`, `(0 5 1
3)`, `(0 5)(1 3)(2 4)`. -/
def pES4b60 : Fin 6 → Fin 6 := id
def pES4b61 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 2
def pES4b62 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3
def pES4b63 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 2 | 4 => 3 | 5 => 4
def pES4b64 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pES4b65 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pES4b66 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5
def pES4b67 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2
def pES4b68 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 3
def pES4b69 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5
def pES4b610 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 5 | 5 => 1
def pES4b611 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 0
def pES4b612 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 4
def pES4b613 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 2
def pES4b614 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 0
def pES4b615 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 1
def pES4b616 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 5
def pES4b617 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 0 | 5 => 3
def pES4b618 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0
def pES4b619 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 5 | 3 => 0 | 4 => 3 | 5 => 1
def pES4b620 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 2
def pES4b621 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4
def pES4b622 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 1
def pES4b623 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 0

def permES4b6 : Fin 24 → Fin 6 → Fin 6
  | 0 => pES4b60
  | 1 => pES4b61
  | 2 => pES4b62
  | 3 => pES4b63
  | 4 => pES4b64
  | 5 => pES4b65
  | 6 => pES4b66
  | 7 => pES4b67
  | 8 => pES4b68
  | 9 => pES4b69
  | 10 => pES4b610
  | 11 => pES4b611
  | 12 => pES4b612
  | 13 => pES4b613
  | 14 => pES4b614
  | 15 => pES4b615
  | 16 => pES4b616
  | 17 => pES4b617
  | 18 => pES4b618
  | 19 => pES4b619
  | 20 => pES4b620
  | 21 => pES4b621
  | 22 => pES4b622
  | _ => pES4b623

def permEinvS4b6 : Fin 24 → Fin 6 → Fin 6
  | 0 => pES4b60
  | 1 => pES4b63
  | 2 => pES4b62
  | 3 => pES4b61
  | 4 => pES4b64
  | 5 => pES4b65
  | 6 => pES4b66
  | 7 => pES4b67
  | 8 => pES4b68
  | 9 => pES4b616
  | 10 => pES4b612
  | 11 => pES4b620
  | 12 => pES4b610
  | 13 => pES4b619
  | 14 => pES4b622
  | 15 => pES4b615
  | 16 => pES4b69
  | 17 => pES4b617
  | 18 => pES4b621
  | 19 => pES4b613
  | 20 => pES4b611
  | 21 => pES4b618
  | 22 => pES4b614
  | _ => pES4b623

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES4b6 (i : Fin 24) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permES4b6 i) (permEinvS4b6 i) (by revert i; decide)

/-- The `3` permutations that must *not* be automorphisms: `(1 2 5 3 4)`, `(0 2 5 1)`, `(0 5 2 1 3
4)`. Every subgroup properly containing the group above contains one of them, so a magma admitting
the group and not these has that group as its automorphism group exactly. -/
def pXS4b60 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 3
def pXS4b61 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 1
def pXS4b62 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 2
def pXS4b60inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 2
def pXS4b61inv : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 2
def pXS4b62inv : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 0

def permXS4b6 : Fin 3 → Fin 6 → Fin 6
  | 0 => pXS4b60
  | 1 => pXS4b61
  | 2 => pXS4b62

def permXinvS4b6 : Fin 3 → Fin 6 → Fin 6
  | 0 => pXS4b60inv
  | 1 => pXS4b61inv
  | 2 => pXS4b62inv

def eXS4b6 (i : Fin 3) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXS4b6 i) (permXinvS4b6 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `3`, so an invariant
operation is `3` values. -/
def repS4b6 : Fin 3 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS4b6 : Fin 6 → Fin 6 → Fin 3 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 0, 4 => (2, 2)
  | 0, 5 => (2, 3)
  | 1, 0 => (1, 4)
  | 1, 1 => (0, 4)
  | 1, 2 => (2, 4)
  | 1, 3 => (2, 5)
  | 1, 4 => (2, 6)
  | 1, 5 => (2, 7)
  | 2, 0 => (2, 8)
  | 2, 1 => (2, 9)
  | 2, 2 => (0, 8)
  | 2, 3 => (2, 10)
  | 2, 4 => (1, 8)
  | 2, 5 => (2, 11)
  | 3, 0 => (2, 12)
  | 3, 1 => (2, 13)
  | 3, 2 => (2, 14)
  | 3, 3 => (0, 12)
  | 3, 4 => (2, 15)
  | 3, 5 => (1, 12)
  | 4, 0 => (2, 16)
  | 4, 1 => (2, 17)
  | 4, 2 => (1, 16)
  | 4, 3 => (2, 18)
  | 4, 4 => (0, 16)
  | 4, 5 => (2, 19)
  | 5, 0 => (2, 20)
  | 5, 1 => (2, 21)
  | 5, 2 => (2, 22)
  | 5, 3 => (1, 20)
  | 5, 4 => (2, 23)
  | 5, 5 => (0, 20)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS4b60 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4b60 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS4b61 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4b61 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxS4b62 : Fin 1 → Fin 24
  | 0 => 0

/-- The `3` orbit values named by the family's arguments. -/
def decS4b6 (a b : Fin 2) (c : Fin 6) : Fin 3 → Fin 6
  | 0 => valS4b60 a
  | 1 => valS4b61 b
  | 2 => c

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS4b6_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS4b6 (a b : Fin 2) (c : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valS4b60 a
  | 0, 1 => valS4b61 b
  | 0, 2 => c
  | 0, 3 => pES4b61 c
  | 0, 4 => pES4b62 c
  | 0, 5 => pES4b63 c
  | 1, 0 => pES4b64 (valS4b61 b)
  | 1, 1 => pES4b64 (valS4b60 a)
  | 1, 2 => pES4b64 c
  | 1, 3 => pES4b65 c
  | 1, 4 => pES4b66 c
  | 1, 5 => pES4b67 c
  | 2, 0 => pES4b68 c
  | 2, 1 => pES4b69 c
  | 2, 2 => pES4b68 (valS4b60 a)
  | 2, 3 => pES4b610 c
  | 2, 4 => pES4b68 (valS4b61 b)
  | 2, 5 => pES4b611 c
  | 3, 0 => pES4b612 c
  | 3, 1 => pES4b613 c
  | 3, 2 => pES4b614 c
  | 3, 3 => pES4b612 (valS4b60 a)
  | 3, 4 => pES4b615 c
  | 3, 5 => pES4b612 (valS4b61 b)
  | 4, 0 => pES4b616 c
  | 4, 1 => pES4b617 c
  | 4, 2 => pES4b616 (valS4b61 b)
  | 4, 3 => pES4b618 c
  | 4, 4 => pES4b616 (valS4b60 a)
  | 4, 5 => pES4b619 c
  | 5, 0 => pES4b620 c
  | 5, 1 => pES4b621 c
  | 5, 2 => pES4b622 c
  | 5, 3 => pES4b620 (valS4b61 b)
  | 5, 4 => pES4b623 c
  | 5, 5 => pES4b620 (valS4b60 a)

theorem tabS4b6_eq_transport (a b : Fin 2) (c : Fin 6) :
    tabS4b6 a b c = Magma.transport permES4b6 trS4b6 (decS4b6 a b c) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `8` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `24` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS4b6 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabS4b6 0 0 3
  | 1 => tabS4b6 0 0 5
  | 2 => tabS4b6 0 1 3
  | 3 => tabS4b6 0 1 5
  | 4 => tabS4b6 1 0 3
  | 5 => tabS4b6 1 0 5
  | 6 => tabS4b6 1 1 3
  | 7 => tabS4b6 1 1 5

/-- Which of the `8` members a given invariant tuple is, so that `mem_of_isExactS4b6` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS4b6 : Array Nat := #[
  0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 0, 4, 0, 5, 0, 0, 0, 6, 0, 7]

/-- The arguments as one mixed-radix index, which is how `rankArrS4b6` is addressed. -/
def encTS4b6 (a b : Fin 2) (c : Fin 6) : Nat :=
  a.1 * 12 +
    b.1 * 6 +
    c.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS4b6 (a b : Fin 2) (c : Fin 6) : Fin 8 :=
  ⟨min (rankArrS4b6.getD (encTS4b6 a b c) 0) 7, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS4b6 (i : Fin 8) : Magma (Fin 6) := Magma.mk (memS4b6 i)

theorem exactS4b6_isEndo (i : Fin 8) (j : Fin 24) : (exactS4b6 i).IsEndo ⇑(eES4b6 j) := by
  simp only [eES4b6, coe_permOf]; revert i j; native_decide

theorem exactS4b6_not_isEndo (i : Fin 8) (j : Fin 3) : ¬ (exactS4b6 i).IsEndo ⇑(eXS4b6 j) := by
  simp only [eXS4b6, coe_permOf]; revert i j; native_decide

/-- `rankS4b6` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS4b6` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS4b6 (a b : Fin 2) (c : Fin 6)
    (h : Magma.isExact (tabS4b6 a b c) permES4b6 permXS4b6 = true) :
    memS4b6 (rankS4b6 a b c) = tabS4b6 a b c := by
  revert h; revert a b c; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `8` listed
members. -/
theorem mem_of_isExactS4b6 (a b : Fin 2) (c : Fin 6)
    (h : Magma.isExact (tabS4b6 a b c) permES4b6 permXS4b6 = true) :
    ∃ i, memS4b6 i = tabS4b6 a b c :=
  ⟨_, mem_rankS4b6 a b c h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS4b6`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS4b6` turns that into a member index. -/
theorem exists_exactS4b6 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eES4b6 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS4b6 i)) : ∃ i, exactS4b6 i = M := by
  simp only [eES4b6, coe_permOf] at hE
  simp only [eXS4b6, coe_permOf] at hX
  have hop : M.op = Magma.transport permES4b6 trS4b6 (fun i ↦ M.op (repS4b6 i).1 (repS4b6 i).2) :=
    Magma.op_eq_transport (rep := repS4b6) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES4b6) (idx := stabIdxS4b60) (a := (repS4b6 0).1) (b := (repS4b6 0).2)
    (val := valS4b60) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES4b6) (idx := stabIdxS4b61) (a := (repS4b6 1).1) (b := (repS4b6 1).2)
    (val := valS4b61) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES4b6) (idx := stabIdxS4b62) (a := (repS4b6 2).1) (b := (repS4b6 2).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decS4b6 a b c = fun i ↦ M.op (repS4b6 i).1 (repS4b6 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have key : tabS4b6 a b c = M.op := by
    rw [tabS4b6_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS4b6 a b c) permES4b6 permXS4b6 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS4b6 a b c hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`24` group of `Magma.permES4b6`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS4b6 {L L' : Law.NatMagmaLaw} {i : Fin 8}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactS4b6 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactS4b6 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS4b6 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS4b6
    (fun k ↦ (Magma.exactS4b6_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS4b6_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
