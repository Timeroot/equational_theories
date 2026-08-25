import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S3` on `Fin 4`

One class of `Definability/ExactAut4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`6` group `⟨(1 2 3), (2 3)⟩` -/

/-- The `6` elements of the group: `()`, `(2 3)`, `(1 2)`, `(1 2 3)`, `(1 3 2)`, `(1 3)`. -/
def pES30 : Fin 4 → Fin 4 := id
def pES31 : Fin 4 → Fin 4 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2
def pES32 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pES33 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1
def pES34 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2
def pES35 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1

def permES3 : Fin 6 → Fin 4 → Fin 4
  | 0 => pES30
  | 1 => pES31
  | 2 => pES32
  | 3 => pES33
  | 4 => pES34
  | 5 => pES35

def permEinvS3 : Fin 6 → Fin 4 → Fin 4
  | 0 => pES30
  | 1 => pES31
  | 2 => pES32
  | 3 => pES34
  | 4 => pES33
  | 5 => pES35

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES3 (i : Fin 6) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permES3 i) (permEinvS3 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3)(1 2)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXS30 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0
def pXS30inv : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permXS3 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXS30

def permXinvS3 : Fin 1 → Fin 4 → Fin 4
  | 0 => pXS30inv

def eXS3 (i : Fin 1) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permXS3 i) (permXinvS3 i) (by revert i; decide)

/-- One representative per orbit of the group on the `16` cells; there are `5`, so an invariant
operation is `5` values. -/
def repS3 : Fin 5 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS3 : Fin 4 → Fin 4 → Fin 5 × Fin 6
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 2)
  | 0, 3 => (1, 4)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (4, 1)
  | 2, 0 => (2, 2)
  | 2, 1 => (4, 2)
  | 2, 2 => (3, 2)
  | 2, 3 => (4, 3)
  | 3, 0 => (2, 4)
  | 3, 1 => (4, 4)
  | 3, 2 => (4, 5)
  | 3, 3 => (3, 4)

/-- The `6` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS30 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS30 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS31 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def valS31 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS32 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def valS32 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS33 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def valS33 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxS34 : Fin 1 → Fin 6
  | 0 => 0

/-- The `5` orbit values named by the family's arguments. -/
def decS3 (a : Fin 1) (b c d : Fin 2) (e : Fin 4) : Fin 5 → Fin 4
  | 0 => valS30 a
  | 1 => valS31 b
  | 2 => valS32 c
  | 3 => valS33 d
  | 4 => e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS3_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS3 (a : Fin 1) (b c d : Fin 2) (e : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => valS30 a
  | 0, 1 => valS31 b
  | 0, 2 => pES32 (valS31 b)
  | 0, 3 => pES34 (valS31 b)
  | 1, 0 => valS32 c
  | 1, 1 => valS33 d
  | 1, 2 => e
  | 1, 3 => pES31 e
  | 2, 0 => pES32 (valS32 c)
  | 2, 1 => pES32 e
  | 2, 2 => pES32 (valS33 d)
  | 2, 3 => pES33 e
  | 3, 0 => pES34 (valS32 c)
  | 3, 1 => pES34 e
  | 3, 2 => pES35 e
  | 3, 3 => pES34 (valS33 d)

theorem tabS3_eq_transport (a : Fin 1) (b c d : Fin 2) (e : Fin 4) :
    tabS3 a b c d e = Magma.transport permES3 trS3 (decS3 a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `30` magmas on `Fin 4` whose automorphism group is exactly this group, listed under one
index. Of the `32` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS3 : Fin 30 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabS3 0 0 0 0 0
  | 1 => tabS3 0 0 0 0 1
  | 2 => tabS3 0 0 0 0 2
  | 3 => tabS3 0 0 0 0 3
  | 4 => tabS3 0 0 0 1 0
  | 5 => tabS3 0 0 0 1 1
  | 6 => tabS3 0 0 0 1 2
  | 7 => tabS3 0 0 0 1 3
  | 8 => tabS3 0 0 1 0 0
  | 9 => tabS3 0 0 1 0 1
  | 10 => tabS3 0 0 1 0 2
  | 11 => tabS3 0 0 1 0 3
  | 12 => tabS3 0 0 1 1 0
  | 13 => tabS3 0 0 1 1 2
  | 14 => tabS3 0 0 1 1 3
  | 15 => tabS3 0 1 0 0 0
  | 16 => tabS3 0 1 0 0 1
  | 17 => tabS3 0 1 0 0 2
  | 18 => tabS3 0 1 0 0 3
  | 19 => tabS3 0 1 0 1 0
  | 20 => tabS3 0 1 0 1 1
  | 21 => tabS3 0 1 0 1 3
  | 22 => tabS3 0 1 1 0 0
  | 23 => tabS3 0 1 1 0 1
  | 24 => tabS3 0 1 1 0 2
  | 25 => tabS3 0 1 1 0 3
  | 26 => tabS3 0 1 1 1 0
  | 27 => tabS3 0 1 1 1 1
  | 28 => tabS3 0 1 1 1 2
  | _ => tabS3 0 1 1 1 3

/-- Which of the `30` members a given invariant tuple is, so that `mem_of_isExactS3` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS3 : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14, 15, 16, 17, 18, 19, 20, 0, 21, 22, 23, 24,
  25, 26, 27, 28, 29]

/-- The arguments as one mixed-radix index, which is how `rankArrS3` is addressed. -/
def encTS3 (a : Fin 1) (b c d : Fin 2) (e : Fin 4) : Nat :=
  a.1 * 32 +
    b.1 * 16 +
    c.1 * 8 +
    d.1 * 4 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS3 (a : Fin 1) (b c d : Fin 2) (e : Fin 4) : Fin 30 :=
  ⟨min (rankArrS3.getD (encTS3 a b c d e) 0) 29, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS3 (i : Fin 30) : Magma (Fin 4) := Magma.mk (memS3 i)

theorem exactS3_isEndo (i : Fin 30) (j : Fin 6) : (exactS3 i).IsEndo ⇑(eES3 j) := by
  simp only [eES3, coe_permOf]; revert i j; native_decide

theorem exactS3_not_isEndo (i : Fin 30) (j : Fin 1) : ¬ (exactS3 i).IsEndo ⇑(eXS3 j) := by
  simp only [eXS3, coe_permOf]; revert i j; native_decide

/-- `rankS3` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS3` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS3 (a : Fin 1) (b c d : Fin 2) (e : Fin 4)
    (h : Magma.isExact (tabS3 a b c d e) permES3 permXS3 = true) :
    memS3 (rankS3 a b c d e) = tabS3 a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `30` listed
members. -/
theorem mem_of_isExactS3 (a : Fin 1) (b c d : Fin 2) (e : Fin 4)
    (h : Magma.isExact (tabS3 a b c d e) permES3 permXS3 = true) :
    ∃ i, memS3 i = tabS3 a b c d e :=
  ⟨_, mem_rankS3 a b c d e h⟩

/-- A magma on `Fin 4` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS3`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS3` turns that into a member index. -/
theorem exists_exactS3 {M : Magma (Fin 4)} (hE : ∀ i, M.IsEndo ⇑(eES3 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS3 i)) : ∃ i, exactS3 i = M := by
  simp only [eES3, coe_permOf] at hE
  simp only [eXS3, coe_permOf] at hX
  have hop : M.op = Magma.transport permES3 trS3 (fun i ↦ M.op (repS3 i).1 (repS3 i).2) :=
    Magma.op_eq_transport (rep := repS3) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES3) (idx := stabIdxS30) (a := (repS3 0).1) (b := (repS3 0).2)
    (val := valS30) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES3) (idx := stabIdxS31) (a := (repS3 1).1) (b := (repS3 1).2)
    (val := valS31) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES3) (idx := stabIdxS32) (a := (repS3 2).1) (b := (repS3 2).2)
    (val := valS32) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES3) (idx := stabIdxS33) (a := (repS3 3).1) (b := (repS3 3).2)
    (val := valS33) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES3) (idx := stabIdxS34) (a := (repS3 4).1) (b := (repS3 4).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decS3 a b c d e = fun i ↦ M.op (repS3 i).1 (repS3 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tabS3 a b c d e = M.op := by
    rw [tabS3_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS3 a b c d e) permES3 permXS3 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS3 a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose automorphism
group is exactly the order-`6` group of `Magma.permES3`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS3 {L L' : Law.NatMagmaLaw} {i : Fin 30}
    (hsrc : @satisfies _ (Fin 4) (Magma.exactS3 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.exactS3 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS3 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS3
    (fun k ↦ (Magma.exactS3_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS3_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
