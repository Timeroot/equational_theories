import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S4a6` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`24` group `⟨(0 1 2)(3 4 5), (0 1 4)(2 5 3), (0 1 5 3)(2 4)⟩` -/

/-- The `24` elements of the group: `()`, `(1 2)(3 4)`, `(1 3)(2 4)`, `(1 4)(2 3)`, `(0 1)(3 5)`,
`(0 1 2)(3 4 5)`, `(0 1 4)(2 5 3)`, `(0 1 5 3)(2 4)`, `(0 2 1)(3 5 4)`, `(0 2)(4 5)`, `(0 2 5 4)(1
3)`, `(0 2 3)(1 5 4)`, `(0 3 5 1)(2 4)`, `(0 3 4)(1 2 5)`, `(0 3 2)(1 4 5)`, `(0 3)(1 5)`, `(0 4
1)(2 3 5)`, `(0 4)(2 5)`, `(0 4 5 2)(1 3)`, `(0 4 3)(1 5 2)`, `(0 5)(2 4)`, `(0 5)(1 2 3 4)`, `(0
5)(1 3)`, `(0 5)(1 4 3 2)`. -/
def pES4a60 : Fin 6 → Fin 6 := id
def pES4a61 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5
def pES4a62 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5
def pES4a63 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5
def pES4a64 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pES4a65 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pES4a66 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 3
def pES4a67 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 3
def pES4a68 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pES4a69 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pES4a610 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 0 | 5 => 4
def pES4a611 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 4
def pES4a612 : Fin 6 → Fin 6 | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 1
def pES4a613 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 1
def pES4a614 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 5 | 5 => 1
def pES4a615 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 1
def pES4a616 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 2
def pES4a617 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 2
def pES4a618 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 2
def pES4a619 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 2
def pES4a620 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 0
def pES4a621 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 0
def pES4a622 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 0
def pES4a623 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 0

def permES4a6 : Fin 24 → Fin 6 → Fin 6
  | 0 => pES4a60
  | 1 => pES4a61
  | 2 => pES4a62
  | 3 => pES4a63
  | 4 => pES4a64
  | 5 => pES4a65
  | 6 => pES4a66
  | 7 => pES4a67
  | 8 => pES4a68
  | 9 => pES4a69
  | 10 => pES4a610
  | 11 => pES4a611
  | 12 => pES4a612
  | 13 => pES4a613
  | 14 => pES4a614
  | 15 => pES4a615
  | 16 => pES4a616
  | 17 => pES4a617
  | 18 => pES4a618
  | 19 => pES4a619
  | 20 => pES4a620
  | 21 => pES4a621
  | 22 => pES4a622
  | _ => pES4a623

def permEinvS4a6 : Fin 24 → Fin 6 → Fin 6
  | 0 => pES4a60
  | 1 => pES4a61
  | 2 => pES4a62
  | 3 => pES4a63
  | 4 => pES4a64
  | 5 => pES4a68
  | 6 => pES4a616
  | 7 => pES4a612
  | 8 => pES4a65
  | 9 => pES4a69
  | 10 => pES4a618
  | 11 => pES4a614
  | 12 => pES4a67
  | 13 => pES4a619
  | 14 => pES4a611
  | 15 => pES4a615
  | 16 => pES4a66
  | 17 => pES4a617
  | 18 => pES4a610
  | 19 => pES4a613
  | 20 => pES4a620
  | 21 => pES4a623
  | 22 => pES4a622
  | _ => pES4a621

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES4a6 (i : Fin 24) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permES4a6 i) (permEinvS4a6 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(0 5 3 2)(1 4)`, `(0 5)(1 4)(2 3)`.
Every subgroup properly containing the group above contains one of them, so a magma admitting the
group and not these has that group as its automorphism group exactly. -/
def pXS4a60 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 3
def pXS4a61 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0
def pXS4a60inv : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 0
def pXS4a61inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0

def permXS4a6 : Fin 2 → Fin 6 → Fin 6
  | 0 => pXS4a60
  | 1 => pXS4a61

def permXinvS4a6 : Fin 2 → Fin 6 → Fin 6
  | 0 => pXS4a60inv
  | 1 => pXS4a61inv

def eXS4a6 (i : Fin 2) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXS4a6 i) (permXinvS4a6 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `3`, so an invariant
operation is `3` values. -/
def repS4a6 : Fin 3 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS4a6 : Fin 6 → Fin 6 → Fin 3 × Fin 24
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 0, 4 => (1, 3)
  | 0, 5 => (2, 0)
  | 1, 0 => (1, 4)
  | 1, 1 => (0, 4)
  | 1, 2 => (1, 5)
  | 1, 3 => (2, 4)
  | 1, 4 => (1, 6)
  | 1, 5 => (1, 7)
  | 2, 0 => (1, 8)
  | 2, 1 => (1, 9)
  | 2, 2 => (0, 8)
  | 2, 3 => (1, 10)
  | 2, 4 => (2, 8)
  | 2, 5 => (1, 11)
  | 3, 0 => (1, 12)
  | 3, 1 => (2, 12)
  | 3, 2 => (1, 13)
  | 3, 3 => (0, 12)
  | 3, 4 => (1, 14)
  | 3, 5 => (1, 15)
  | 4, 0 => (1, 16)
  | 4, 1 => (1, 17)
  | 4, 2 => (2, 16)
  | 4, 3 => (1, 18)
  | 4, 4 => (0, 16)
  | 4, 5 => (1, 19)
  | 5, 0 => (2, 20)
  | 5, 1 => (1, 20)
  | 5, 2 => (1, 21)
  | 5, 3 => (1, 22)
  | 5, 4 => (1, 23)
  | 5, 5 => (0, 20)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `5`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS4a60 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4a60 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 5

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxS4a61 : Fin 1 → Fin 24
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `5`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS4a62 : Fin 4 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS4a62 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 5

/-- The `3` orbit values named by the family's arguments. -/
def decS4a6 (a : Fin 2) (b : Fin 6) (c : Fin 2) : Fin 3 → Fin 6
  | 0 => valS4a60 a
  | 1 => b
  | 2 => valS4a62 c

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS4a6_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS4a6 (a : Fin 2) (b : Fin 6) (c : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valS4a60 a
  | 0, 1 => b
  | 0, 2 => pES4a61 b
  | 0, 3 => pES4a62 b
  | 0, 4 => pES4a63 b
  | 0, 5 => valS4a62 c
  | 1, 0 => pES4a64 b
  | 1, 1 => pES4a64 (valS4a60 a)
  | 1, 2 => pES4a65 b
  | 1, 3 => pES4a64 (valS4a62 c)
  | 1, 4 => pES4a66 b
  | 1, 5 => pES4a67 b
  | 2, 0 => pES4a68 b
  | 2, 1 => pES4a69 b
  | 2, 2 => pES4a68 (valS4a60 a)
  | 2, 3 => pES4a610 b
  | 2, 4 => pES4a68 (valS4a62 c)
  | 2, 5 => pES4a611 b
  | 3, 0 => pES4a612 b
  | 3, 1 => pES4a612 (valS4a62 c)
  | 3, 2 => pES4a613 b
  | 3, 3 => pES4a612 (valS4a60 a)
  | 3, 4 => pES4a614 b
  | 3, 5 => pES4a615 b
  | 4, 0 => pES4a616 b
  | 4, 1 => pES4a617 b
  | 4, 2 => pES4a616 (valS4a62 c)
  | 4, 3 => pES4a618 b
  | 4, 4 => pES4a616 (valS4a60 a)
  | 4, 5 => pES4a619 b
  | 5, 0 => pES4a620 (valS4a62 c)
  | 5, 1 => pES4a620 b
  | 5, 2 => pES4a621 b
  | 5, 3 => pES4a622 b
  | 5, 4 => pES4a623 b
  | 5, 5 => pES4a620 (valS4a60 a)

theorem tabS4a6_eq_transport (a : Fin 2) (b : Fin 6) (c : Fin 2) :
    tabS4a6 a b c = Magma.transport permES4a6 trS4a6 (decS4a6 a b c) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `8` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `24` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS4a6 : Fin 8 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabS4a6 0 2 0
  | 1 => tabS4a6 0 2 1
  | 2 => tabS4a6 0 4 0
  | 3 => tabS4a6 0 4 1
  | 4 => tabS4a6 1 2 0
  | 5 => tabS4a6 1 2 1
  | 6 => tabS4a6 1 4 0
  | 7 => tabS4a6 1 4 1

/-- Which of the `8` members a given invariant tuple is, so that `mem_of_isExactS4a6` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS4a6 : Array Nat := #[
  0, 0, 0, 0, 0, 1, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 4, 5, 0, 0, 6, 7, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArrS4a6` is addressed. -/
def encTS4a6 (a : Fin 2) (b : Fin 6) (c : Fin 2) : Nat :=
  a.1 * 12 +
    b.1 * 2 +
    c.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS4a6 (a : Fin 2) (b : Fin 6) (c : Fin 2) : Fin 8 :=
  ⟨min (rankArrS4a6.getD (encTS4a6 a b c) 0) 7, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS4a6 (i : Fin 8) : Magma (Fin 6) := Magma.mk (memS4a6 i)

theorem exactS4a6_isEndo (i : Fin 8) (j : Fin 24) : (exactS4a6 i).IsEndo ⇑(eES4a6 j) := by
  simp only [eES4a6, coe_permOf]; revert i j; native_decide

theorem exactS4a6_not_isEndo (i : Fin 8) (j : Fin 2) : ¬ (exactS4a6 i).IsEndo ⇑(eXS4a6 j) := by
  simp only [eXS4a6, coe_permOf]; revert i j; native_decide

/-- `rankS4a6` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS4a6` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS4a6 (a : Fin 2) (b : Fin 6) (c : Fin 2)
    (h : Magma.isExact (tabS4a6 a b c) permES4a6 permXS4a6 = true) :
    memS4a6 (rankS4a6 a b c) = tabS4a6 a b c := by
  revert h; revert a b c; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `8` listed
members. -/
theorem mem_of_isExactS4a6 (a : Fin 2) (b : Fin 6) (c : Fin 2)
    (h : Magma.isExact (tabS4a6 a b c) permES4a6 permXS4a6 = true) :
    ∃ i, memS4a6 i = tabS4a6 a b c :=
  ⟨_, mem_rankS4a6 a b c h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS4a6`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS4a6` turns that into a member index. -/
theorem exists_exactS4a6 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eES4a6 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS4a6 i)) : ∃ i, exactS4a6 i = M := by
  simp only [eES4a6, coe_permOf] at hE
  simp only [eXS4a6, coe_permOf] at hX
  have hop : M.op = Magma.transport permES4a6 trS4a6 (fun i ↦ M.op (repS4a6 i).1 (repS4a6 i).2) :=
    Magma.op_eq_transport (rep := repS4a6) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES4a6) (idx := stabIdxS4a60) (a := (repS4a6 0).1) (b := (repS4a6 0).2)
    (val := valS4a60) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES4a6) (idx := stabIdxS4a61) (a := (repS4a6 1).1) (b := (repS4a6 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES4a6) (idx := stabIdxS4a62) (a := (repS4a6 2).1) (b := (repS4a6 2).2)
    (val := valS4a62) hE (by decide) (by decide)
  have hdec : decS4a6 a b c = fun i ↦ M.op (repS4a6 i).1 (repS4a6 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have key : tabS4a6 a b c = M.op := by
    rw [tabS4a6_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS4a6 a b c) permES4a6 permXS4a6 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS4a6 a b c hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`24` group of `Magma.permES4a6`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS4a6 {L L' : Law.NatMagmaLaw} {i : Fin 8}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactS4a6 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactS4a6 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS4a6 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS4a6
    (fun k ↦ (Magma.exactS4a6_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS4a6_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
