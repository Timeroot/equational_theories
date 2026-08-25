import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `F206` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`20` group `⟨(1 2 3 4 5), (2 3 5 4)⟩` -/

/-- The `20` elements of the group: `()`, `(2 3 5 4)`, `(2 4 5 3)`, `(2 5)(3 4)`, `(1 2)(3 5)`, `(1
2 3 4 5)`, `(1 2 4 3)`, `(1 2 5 4)`, `(1 3 4 2)`, `(1 3)(4 5)`, `(1 3 5 2 4)`, `(1 3 2 5)`, `(1 4 5
2)`, `(1 4 3 5)`, `(1 4)(2 3)`, `(1 4 2 5 3)`, `(1 5 4 3 2)`, `(1 5 3 4)`, `(1 5 2 3)`, `(1 5)(2
4)`. -/
def pEF2060 : Fin 6 → Fin 6 := id
def pEF2061 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 2 | 5 => 4
def pEF2062 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 5 | 5 => 3
def pEF2063 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2
def pEF2064 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
def pEF2065 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 1
def pEF2066 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5
def pEF2067 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 4
def pEF2068 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5
def pEF2069 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4
def pEF20610 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 2
def pEF20611 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 4 | 5 => 1
def pEF20612 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 2
def pEF20613 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 1
def pEF20614 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5
def pEF20615 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 2 | 5 => 3
def pEF20616 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4
def pEF20617 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 3
def pEF20618 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 2
def pEF20619 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1

def permEF206 : Fin 20 → Fin 6 → Fin 6
  | 0 => pEF2060
  | 1 => pEF2061
  | 2 => pEF2062
  | 3 => pEF2063
  | 4 => pEF2064
  | 5 => pEF2065
  | 6 => pEF2066
  | 7 => pEF2067
  | 8 => pEF2068
  | 9 => pEF2069
  | 10 => pEF20610
  | 11 => pEF20611
  | 12 => pEF20612
  | 13 => pEF20613
  | 14 => pEF20614
  | 15 => pEF20615
  | 16 => pEF20616
  | 17 => pEF20617
  | 18 => pEF20618
  | _ => pEF20619

def permEinvF206 : Fin 20 → Fin 6 → Fin 6
  | 0 => pEF2060
  | 1 => pEF2062
  | 2 => pEF2061
  | 3 => pEF2063
  | 4 => pEF2064
  | 5 => pEF20616
  | 6 => pEF2068
  | 7 => pEF20612
  | 8 => pEF2066
  | 9 => pEF2069
  | 10 => pEF20615
  | 11 => pEF20618
  | 12 => pEF2067
  | 13 => pEF20617
  | 14 => pEF20614
  | 15 => pEF20610
  | 16 => pEF2065
  | 17 => pEF20613
  | 18 => pEF20611
  | _ => pEF20619

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEF206 (i : Fin 20) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permEF206 i) (permEinvF206 i) (by revert i; decide)

/-- The `2` permutations that must *not* be automorphisms: `(1 2 5 3 4)`, `(0 5 1 4 2 3)`. Every
subgroup properly containing the group above contains one of them, so a magma admitting the group
and not these has that group as its automorphism group exactly. -/
def pXF2060 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 1 | 5 => 3
def pXF2061 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 1
def pXF2060inv : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 2
def pXF2061inv : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 0

def permXF206 : Fin 2 → Fin 6 → Fin 6
  | 0 => pXF2060
  | 1 => pXF2061

def permXinvF206 : Fin 2 → Fin 6 → Fin 6
  | 0 => pXF2060inv
  | 1 => pXF2061inv

def eXF206 (i : Fin 2) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXF206 i) (permXinvF206 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `5`, so an invariant
operation is `5` values. -/
def repF206 : Fin 5 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trF206 : Fin 6 → Fin 6 → Fin 5 × Fin 20
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 4)
  | 0, 3 => (1, 8)
  | 0, 4 => (1, 12)
  | 0, 5 => (1, 16)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (4, 1)
  | 1, 4 => (4, 2)
  | 1, 5 => (4, 3)
  | 2, 0 => (2, 4)
  | 2, 1 => (4, 4)
  | 2, 2 => (3, 4)
  | 2, 3 => (4, 5)
  | 2, 4 => (4, 6)
  | 2, 5 => (4, 7)
  | 3, 0 => (2, 8)
  | 3, 1 => (4, 8)
  | 3, 2 => (4, 9)
  | 3, 3 => (3, 8)
  | 3, 4 => (4, 10)
  | 3, 5 => (4, 11)
  | 4, 0 => (2, 12)
  | 4, 1 => (4, 12)
  | 4, 2 => (4, 13)
  | 4, 3 => (4, 14)
  | 4, 4 => (3, 12)
  | 4, 5 => (4, 15)
  | 5, 0 => (2, 16)
  | 5, 1 => (4, 16)
  | 5, 2 => (4, 17)
  | 5, 3 => (4, 18)
  | 5, 4 => (4, 19)
  | 5, 5 => (3, 16)

/-- The `20` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxF2060 : Fin 20 → Fin 20
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
  | _ => 19
def valF2060 : Fin 1 → Fin 6
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxF2061 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valF2061 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxF2062 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valF2062 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxF2063 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valF2063 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdxF2064 : Fin 1 → Fin 20
  | 0 => 0

/-- The `5` orbit values named by the family's arguments. -/
def decF206 (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Fin 5 → Fin 6
  | 0 => valF2060 a
  | 1 => valF2061 b
  | 2 => valF2062 c
  | 3 => valF2063 d
  | 4 => e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabF206_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabF206 (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valF2060 a
  | 0, 1 => valF2061 b
  | 0, 2 => pEF2064 (valF2061 b)
  | 0, 3 => pEF2068 (valF2061 b)
  | 0, 4 => pEF20612 (valF2061 b)
  | 0, 5 => pEF20616 (valF2061 b)
  | 1, 0 => valF2062 c
  | 1, 1 => valF2063 d
  | 1, 2 => e
  | 1, 3 => pEF2061 e
  | 1, 4 => pEF2062 e
  | 1, 5 => pEF2063 e
  | 2, 0 => pEF2064 (valF2062 c)
  | 2, 1 => pEF2064 e
  | 2, 2 => pEF2064 (valF2063 d)
  | 2, 3 => pEF2065 e
  | 2, 4 => pEF2066 e
  | 2, 5 => pEF2067 e
  | 3, 0 => pEF2068 (valF2062 c)
  | 3, 1 => pEF2068 e
  | 3, 2 => pEF2069 e
  | 3, 3 => pEF2068 (valF2063 d)
  | 3, 4 => pEF20610 e
  | 3, 5 => pEF20611 e
  | 4, 0 => pEF20612 (valF2062 c)
  | 4, 1 => pEF20612 e
  | 4, 2 => pEF20613 e
  | 4, 3 => pEF20614 e
  | 4, 4 => pEF20612 (valF2063 d)
  | 4, 5 => pEF20615 e
  | 5, 0 => pEF20616 (valF2062 c)
  | 5, 1 => pEF20616 e
  | 5, 2 => pEF20617 e
  | 5, 3 => pEF20618 e
  | 5, 4 => pEF20619 e
  | 5, 5 => pEF20616 (valF2063 d)

theorem tabF206_eq_transport (a : Fin 1) (b c d : Fin 2) (e : Fin 6) :
    tabF206 a b c d e = Magma.transport permEF206 trF206 (decF206 a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `24` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `48` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memF206 : Fin 24 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabF206 0 0 0 0 3
  | 1 => tabF206 0 0 0 0 4
  | 2 => tabF206 0 0 0 0 5
  | 3 => tabF206 0 0 0 1 3
  | 4 => tabF206 0 0 0 1 4
  | 5 => tabF206 0 0 0 1 5
  | 6 => tabF206 0 0 1 0 3
  | 7 => tabF206 0 0 1 0 4
  | 8 => tabF206 0 0 1 0 5
  | 9 => tabF206 0 0 1 1 3
  | 10 => tabF206 0 0 1 1 4
  | 11 => tabF206 0 0 1 1 5
  | 12 => tabF206 0 1 0 0 3
  | 13 => tabF206 0 1 0 0 4
  | 14 => tabF206 0 1 0 0 5
  | 15 => tabF206 0 1 0 1 3
  | 16 => tabF206 0 1 0 1 4
  | 17 => tabF206 0 1 0 1 5
  | 18 => tabF206 0 1 1 0 3
  | 19 => tabF206 0 1 1 0 4
  | 20 => tabF206 0 1 1 0 5
  | 21 => tabF206 0 1 1 1 3
  | 22 => tabF206 0 1 1 1 4
  | _ => tabF206 0 1 1 1 5

/-- Which of the `24` members a given invariant tuple is, so that `mem_of_isExactF206` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrF206 : Array Nat := #[
  0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 4, 5, 0, 0, 0, 6, 7, 8, 0, 0, 0, 9, 10, 11, 0, 0, 0, 12, 13, 14,
  0, 0, 0, 15, 16, 17, 0, 0, 0, 18, 19, 20, 0, 0, 0, 21, 22, 23]

/-- The arguments as one mixed-radix index, which is how `rankArrF206` is addressed. -/
def encTF206 (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Nat :=
  a.1 * 48 +
    b.1 * 24 +
    c.1 * 12 +
    d.1 * 6 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankF206 (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Fin 24 :=
  ⟨min (rankArrF206.getD (encTF206 a b c d e) 0) 23, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactF206 (i : Fin 24) : Magma (Fin 6) := Magma.mk (memF206 i)

theorem exactF206_isEndo (i : Fin 24) (j : Fin 20) : (exactF206 i).IsEndo ⇑(eEF206 j) := by
  simp only [eEF206, coe_permOf]; revert i j; native_decide

theorem exactF206_not_isEndo (i : Fin 24) (j : Fin 2) : ¬ (exactF206 i).IsEndo ⇑(eXF206 j) := by
  simp only [eXF206, coe_permOf]; revert i j; native_decide

/-- `rankF206` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memF206` for the index would be a comparison per tuple and
member. -/
theorem mem_rankF206 (a : Fin 1) (b c d : Fin 2) (e : Fin 6)
    (h : Magma.isExact (tabF206 a b c d e) permEF206 permXF206 = true) :
    memF206 (rankF206 a b c d e) = tabF206 a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `24` listed
members. -/
theorem mem_of_isExactF206 (a : Fin 1) (b c d : Fin 2) (e : Fin 6)
    (h : Magma.isExact (tabF206 a b c d e) permEF206 permXF206 = true) :
    ∃ i, memF206 i = tabF206 a b c d e :=
  ⟨_, mem_rankF206 a b c d e h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactF206`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactF206` turns that into a member index. -/
theorem exists_exactF206 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eEF206 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXF206 i)) : ∃ i, exactF206 i = M := by
  simp only [eEF206, coe_permOf] at hE
  simp only [eXF206, coe_permOf] at hX
  have hop : M.op = Magma.transport permEF206 trF206 (fun i ↦ M.op (repF206 i).1 (repF206 i).2) :=
    Magma.op_eq_transport (rep := repF206) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEF206) (idx := stabIdxF2060) (a := (repF206 0).1) (b := (repF206 0).2)
    (val := valF2060) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEF206) (idx := stabIdxF2061) (a := (repF206 1).1) (b := (repF206 1).2)
    (val := valF2061) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEF206) (idx := stabIdxF2062) (a := (repF206 2).1) (b := (repF206 2).2)
    (val := valF2062) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEF206) (idx := stabIdxF2063) (a := (repF206 3).1) (b := (repF206 3).2)
    (val := valF2063) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permEF206) (idx := stabIdxF2064) (a := (repF206 4).1) (b := (repF206 4).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decF206 a b c d e = fun i ↦ M.op (repF206 i).1 (repF206 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tabF206 a b c d e = M.op := by
    rw [tabF206_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabF206 a b c d e) permEF206 permXF206 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactF206 a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`20` group of `Magma.permEF206`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactF206 {L L' : Law.NatMagmaLaw} {i : Fin 24}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactF206 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactF206 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactF206 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactF206
    (fun k ↦ (Magma.exactF206_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactF206_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
