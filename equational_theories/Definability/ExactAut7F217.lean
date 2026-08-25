import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `F217` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`21` group `⟨(0 1 3 4 2 5 6), (1 2 3)(4 5 6)⟩` -/

/-- The `21` elements of the group: `()`, `(1 2 3)(4 5 6)`, `(1 3 2)(4 6 5)`, `(0 1 3 4 2 5 6)`, `(0
1 4)(2 3 5)`, `(0 1 5)(2 4 6)`, `(0 2 6)(3 5 4)`, `(0 2 1 5 3 6 4)`, `(0 2 5)(1 6 3)`, `(0 3 6)(1 2
4)`, `(0 3 2 6 1 4 5)`, `(0 3 4)(1 6 5)`, `(0 4 1)(2 5 3)`, `(0 4 6 3 5 1 2)`, `(0 4 3)(1 5 6)`, `(0
5 1)(2 6 4)`, `(0 5 2)(1 3 6)`, `(0 5 4 1 6 2 3)`, `(0 6 5 2 4 3 1)`, `(0 6 2)(3 4 5)`, `(0 6 3)(1 4
2)`. -/
def pEF2170 : Fin 7 → Fin 7 := id
def pEF2171 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 4
def pEF2172 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5
def pEF2173 : Fin 7 → Fin 7 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 0
def pEF2174 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 5 | 4 => 0 | 5 => 2 | 6 => 6
def pEF2175 : Fin 7 → Fin 7 | 0 => 1 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 6 | 5 => 0 | 6 => 2
def pEF2176 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 6 | 3 => 5 | 4 => 3 | 5 => 4 | 6 => 0
def pEF2177 : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 1 | 3 => 6 | 4 => 0 | 5 => 3 | 6 => 4
def pEF2178 : Fin 7 → Fin 7 | 0 => 2 | 1 => 6 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 0 | 6 => 3
def pEF2179 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 6 | 4 => 1 | 5 => 5 | 6 => 0
def pEF21710 : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 0 | 6 => 1
def pEF21711 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 1 | 6 => 5
def pEF21712 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 2 | 4 => 1 | 5 => 3 | 6 => 6
def pEF21713 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 5 | 4 => 6 | 5 => 1 | 6 => 3
def pEF21714 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 1
def pEF21715 : Fin 7 → Fin 7 | 0 => 5 | 1 => 0 | 2 => 6 | 3 => 3 | 4 => 2 | 5 => 1 | 6 => 4
def pEF21716 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 0 | 3 => 6 | 4 => 4 | 5 => 2 | 6 => 1
def pEF21717 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 4 | 6 => 2
def pEF21718 : Fin 7 → Fin 7 | 0 => 6 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 5
def pEF21719 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3 | 6 => 2
def pEF21720 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 3

def permEF217 : Fin 21 → Fin 7 → Fin 7
  | 0 => pEF2170
  | 1 => pEF2171
  | 2 => pEF2172
  | 3 => pEF2173
  | 4 => pEF2174
  | 5 => pEF2175
  | 6 => pEF2176
  | 7 => pEF2177
  | 8 => pEF2178
  | 9 => pEF2179
  | 10 => pEF21710
  | 11 => pEF21711
  | 12 => pEF21712
  | 13 => pEF21713
  | 14 => pEF21714
  | 15 => pEF21715
  | 16 => pEF21716
  | 17 => pEF21717
  | 18 => pEF21718
  | 19 => pEF21719
  | _ => pEF21720

def permEinvF217 : Fin 21 → Fin 7 → Fin 7
  | 0 => pEF2170
  | 1 => pEF2172
  | 2 => pEF2171
  | 3 => pEF21718
  | 4 => pEF21712
  | 5 => pEF21715
  | 6 => pEF21719
  | 7 => pEF21713
  | 8 => pEF21716
  | 9 => pEF21720
  | 10 => pEF21717
  | 11 => pEF21714
  | 12 => pEF2174
  | 13 => pEF2177
  | 14 => pEF21711
  | 15 => pEF2175
  | 16 => pEF2178
  | 17 => pEF21710
  | 18 => pEF2173
  | 19 => pEF2176
  | _ => pEF2179

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEF217 (i : Fin 21) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permEF217 i) (permEinvF217 i) (by revert i; decide)

/-- The `3` permutations that must *not* be automorphisms: `(1 5 2 6 3 4)`, `(0 5 3)(1 2 4)`, `(0 6
4)(1 3 2)`. Every subgroup properly containing the group above contains one of them, so a magma
admitting the group and not these has that group as its automorphism group exactly. -/
def pXF2170 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 1 | 5 => 2 | 6 => 3
def pXF2171 : Fin 7 → Fin 7 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 3 | 6 => 6
def pXF2172 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 4
def pXF2170inv : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 3 | 5 => 1 | 6 => 2
def pXF2171inv : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 0 | 6 => 6
def pXF2172inv : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 0

def permXF217 : Fin 3 → Fin 7 → Fin 7
  | 0 => pXF2170
  | 1 => pXF2171
  | 2 => pXF2172

def permXinvF217 : Fin 3 → Fin 7 → Fin 7
  | 0 => pXF2170inv
  | 1 => pXF2171inv
  | 2 => pXF2172inv

def eXF217 (i : Fin 3) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXF217 i) (permXinvF217 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `3`, so an invariant
operation is `3` values. -/
def repF217 : Fin 3 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trF217 : Fin 7 → Fin 7 → Fin 3 × Fin 21
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 0, 4 => (2, 0)
  | 0, 5 => (2, 1)
  | 0, 6 => (2, 2)
  | 1, 0 => (2, 4)
  | 1, 1 => (0, 3)
  | 1, 2 => (2, 3)
  | 1, 3 => (1, 3)
  | 1, 4 => (1, 4)
  | 1, 5 => (1, 5)
  | 1, 6 => (2, 5)
  | 2, 0 => (2, 7)
  | 2, 1 => (1, 6)
  | 2, 2 => (0, 6)
  | 2, 3 => (2, 6)
  | 2, 4 => (2, 8)
  | 2, 5 => (1, 7)
  | 2, 6 => (1, 8)
  | 3, 0 => (2, 11)
  | 3, 1 => (2, 9)
  | 3, 2 => (1, 9)
  | 3, 3 => (0, 9)
  | 3, 4 => (1, 10)
  | 3, 5 => (2, 10)
  | 3, 6 => (1, 11)
  | 4, 0 => (1, 12)
  | 4, 1 => (2, 12)
  | 4, 2 => (1, 13)
  | 4, 3 => (2, 14)
  | 4, 4 => (0, 12)
  | 4, 5 => (1, 14)
  | 4, 6 => (2, 13)
  | 5, 0 => (1, 15)
  | 5, 1 => (2, 17)
  | 5, 2 => (2, 15)
  | 5, 3 => (1, 16)
  | 5, 4 => (2, 16)
  | 5, 5 => (0, 15)
  | 5, 6 => (1, 17)
  | 6, 0 => (1, 18)
  | 6, 1 => (1, 19)
  | 6, 2 => (2, 20)
  | 6, 3 => (2, 18)
  | 6, 4 => (1, 20)
  | 6, 5 => (2, 19)
  | 6, 6 => (0, 18)

/-- The `3` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxF2170 : Fin 3 → Fin 21
  | 0 => 0
  | 1 => 1
  | 2 => 2
def valF2170 : Fin 1 → Fin 7
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxF2171 : Fin 1 → Fin 21
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 7`. -/
def stabIdxF2172 : Fin 1 → Fin 21
  | 0 => 0

/-- The `3` orbit values named by the family's arguments. -/
def decF217 (a : Fin 1) (b c : Fin 7) : Fin 3 → Fin 7
  | 0 => valF2170 a
  | 1 => b
  | 2 => c

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabF217_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabF217 (a : Fin 1) (b c : Fin 7) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valF2170 a
  | 0, 1 => b
  | 0, 2 => pEF2171 b
  | 0, 3 => pEF2172 b
  | 0, 4 => c
  | 0, 5 => pEF2171 c
  | 0, 6 => pEF2172 c
  | 1, 0 => pEF2174 c
  | 1, 1 => pEF2173 (valF2170 a)
  | 1, 2 => pEF2173 c
  | 1, 3 => pEF2173 b
  | 1, 4 => pEF2174 b
  | 1, 5 => pEF2175 b
  | 1, 6 => pEF2175 c
  | 2, 0 => pEF2177 c
  | 2, 1 => pEF2176 b
  | 2, 2 => pEF2176 (valF2170 a)
  | 2, 3 => pEF2176 c
  | 2, 4 => pEF2178 c
  | 2, 5 => pEF2177 b
  | 2, 6 => pEF2178 b
  | 3, 0 => pEF21711 c
  | 3, 1 => pEF2179 c
  | 3, 2 => pEF2179 b
  | 3, 3 => pEF2179 (valF2170 a)
  | 3, 4 => pEF21710 b
  | 3, 5 => pEF21710 c
  | 3, 6 => pEF21711 b
  | 4, 0 => pEF21712 b
  | 4, 1 => pEF21712 c
  | 4, 2 => pEF21713 b
  | 4, 3 => pEF21714 c
  | 4, 4 => pEF21712 (valF2170 a)
  | 4, 5 => pEF21714 b
  | 4, 6 => pEF21713 c
  | 5, 0 => pEF21715 b
  | 5, 1 => pEF21717 c
  | 5, 2 => pEF21715 c
  | 5, 3 => pEF21716 b
  | 5, 4 => pEF21716 c
  | 5, 5 => pEF21715 (valF2170 a)
  | 5, 6 => pEF21717 b
  | 6, 0 => pEF21718 b
  | 6, 1 => pEF21719 b
  | 6, 2 => pEF21720 c
  | 6, 3 => pEF21718 c
  | 6, 4 => pEF21720 b
  | 6, 5 => pEF21719 c
  | 6, 6 => pEF21718 (valF2170 a)

theorem tabF217_eq_transport (a : Fin 1) (b c : Fin 7) :
    tabF217 a b c = Magma.transport permEF217 trF217 (decF217 a b c) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `40` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `49` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memF217 : Fin 40 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabF217 0 0 1
  | 1 => tabF217 0 0 2
  | 2 => tabF217 0 0 3
  | 3 => tabF217 0 0 4
  | 4 => tabF217 0 0 5
  | 5 => tabF217 0 0 6
  | 6 => tabF217 0 1 0
  | 7 => tabF217 0 1 1
  | 8 => tabF217 0 1 2
  | 9 => tabF217 0 1 3
  | 10 => tabF217 0 1 5
  | 11 => tabF217 0 1 6
  | 12 => tabF217 0 2 0
  | 13 => tabF217 0 2 1
  | 14 => tabF217 0 2 2
  | 15 => tabF217 0 2 3
  | 16 => tabF217 0 2 4
  | 17 => tabF217 0 2 6
  | 18 => tabF217 0 3 0
  | 19 => tabF217 0 3 1
  | 20 => tabF217 0 3 2
  | 21 => tabF217 0 3 3
  | 22 => tabF217 0 3 4
  | 23 => tabF217 0 3 5
  | 24 => tabF217 0 4 0
  | 25 => tabF217 0 4 2
  | 26 => tabF217 0 4 4
  | 27 => tabF217 0 4 5
  | 28 => tabF217 0 4 6
  | 29 => tabF217 0 5 0
  | 30 => tabF217 0 5 2
  | 31 => tabF217 0 5 4
  | 32 => tabF217 0 5 5
  | 33 => tabF217 0 5 6
  | 34 => tabF217 0 6 0
  | 35 => tabF217 0 6 1
  | 36 => tabF217 0 6 3
  | 37 => tabF217 0 6 4
  | 38 => tabF217 0 6 5
  | _ => tabF217 0 6 6

/-- Which of the `40` members a given invariant tuple is, so that `mem_of_isExactF217` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrF217 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 10, 11, 12, 13, 14, 15, 16, 0, 17, 18, 19, 20, 21, 22, 23,
  0, 24, 0, 25, 0, 26, 27, 28, 29, 0, 30, 0, 31, 32, 33, 34, 35, 0, 36, 37, 38, 39]

/-- The arguments as one mixed-radix index, which is how `rankArrF217` is addressed. -/
def encTF217 (a : Fin 1) (b c : Fin 7) : Nat :=
  a.1 * 49 +
    b.1 * 7 +
    c.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankF217 (a : Fin 1) (b c : Fin 7) : Fin 40 :=
  ⟨min (rankArrF217.getD (encTF217 a b c) 0) 39, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactF217 (i : Fin 40) : Magma (Fin 7) := Magma.mk (memF217 i)

theorem exactF217_isEndo (i : Fin 40) (j : Fin 21) : (exactF217 i).IsEndo ⇑(eEF217 j) := by
  simp only [eEF217, coe_permOf]; revert i j; native_decide

theorem exactF217_not_isEndo (i : Fin 40) (j : Fin 3) : ¬ (exactF217 i).IsEndo ⇑(eXF217 j) := by
  simp only [eXF217, coe_permOf]; revert i j; native_decide

/-- `rankF217` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memF217` for the index would be a comparison per tuple and
member. -/
theorem mem_rankF217 (a : Fin 1) (b c : Fin 7)
    (h : Magma.isExact (tabF217 a b c) permEF217 permXF217 = true) :
    memF217 (rankF217 a b c) = tabF217 a b c := by
  revert h; revert a b c; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `40` listed
members. -/
theorem mem_of_isExactF217 (a : Fin 1) (b c : Fin 7)
    (h : Magma.isExact (tabF217 a b c) permEF217 permXF217 = true) :
    ∃ i, memF217 i = tabF217 a b c :=
  ⟨_, mem_rankF217 a b c h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactF217`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactF217` turns that into a member index. -/
theorem exists_exactF217 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eEF217 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXF217 i)) : ∃ i, exactF217 i = M := by
  simp only [eEF217, coe_permOf] at hE
  simp only [eXF217, coe_permOf] at hX
  have hop : M.op = Magma.transport permEF217 trF217 (fun i ↦ M.op (repF217 i).1 (repF217 i).2) :=
    Magma.op_eq_transport (rep := repF217) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEF217) (idx := stabIdxF2170) (a := (repF217 0).1) (b := (repF217 0).2)
    (val := valF2170) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEF217) (idx := stabIdxF2171) (a := (repF217 1).1) (b := (repF217 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEF217) (idx := stabIdxF2172) (a := (repF217 2).1) (b := (repF217 2).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decF217 a b c = fun i ↦ M.op (repF217 i).1 (repF217 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have key : tabF217 a b c = M.op := by
    rw [tabF217_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabF217 a b c) permEF217 permXF217 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactF217 a b c hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`21` group of `Magma.permEF217`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactF217 {L L' : Law.NatMagmaLaw} {i : Fin 40}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactF217 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactF217 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactF217 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactF217
    (fun k ↦ (Magma.exactF217_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactF217_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
