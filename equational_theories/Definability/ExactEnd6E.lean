import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `E` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1 2)(3 4 5), (0 1 5)(2 3 4)⟩`

`End(M)` is `24` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(1 4)(2 5)`, `(0 1 2)(3 4 5)`, `(0 1 5)(2 3 4)`, `(0 2
1)(3 5 4)`, `(0 2 4)(1 3 5)`, `(0 3)(2 5)`, `(0 3)(1 4)`, `(0 4 5)(1 2 3)`, `(0 4 2)(1 5 3)`, `(0 5
1)(2 4 3)`, `(0 5 4)(1 3 2)`. -/
def pE6E0 : Fin 6 → Fin 6 := id
def pE6E1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 2
def pE6E2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pE6E3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 0
def pE6E4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pE6E5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 1
def pE6E6 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 2
def pE6E7 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5
def pE6E8 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0
def pE6E9 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3
def pE6E10 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1
def pE6E11 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4

def permE6E : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6E0
  | 1 => pE6E1
  | 2 => pE6E2
  | 3 => pE6E3
  | 4 => pE6E4
  | 5 => pE6E5
  | 6 => pE6E6
  | 7 => pE6E7
  | 8 => pE6E8
  | 9 => pE6E9
  | 10 => pE6E10
  | 11 => pE6E11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `24` self-maps that must be endomorphisms: `243510`, `153420`, `513240`,
`423150`, `234501`, `054321`, `504231`, `324051`, `135402`, `045312`, `405132`, `315042`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6E : Fin 24 → Fin 46656
  | 0 => 2510
  | 1 => 3595
  | 2 => 5735
  | 3 => 6820
  | 4 => 9020
  | 5 => 11190
  | 6 => 12245
  | 7 => 14415
  | 8 => 16615
  | 9 => 17700
  | 10 => 19840
  | 11 => 20925
  | 12 => 25085
  | 13 => 26170
  | 14 => 29600
  | 15 => 30685
  | 16 => 31595
  | 17 => 33765
  | 18 => 36110
  | 19 => 38280
  | 20 => 39190
  | 21 => 40275
  | 22 => 43705
  | _ => 44790

def endE6E (j : Fin 24) : Fin 6 → Fin 6 := allMaps6 (eidx6E j)

/-- Indices of the other `46632`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6E : Array Nat := #[
  2510, 3595, 5735, 6820, 9020, 11190, 12245, 14415, 16615, 17700, 19840, 20925, 25085, 26170,
  29600, 30685, 31595, 33765, 36110, 38280, 39190, 40275, 43705, 44790]

def xarr6E : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6E.contains i)

def xidx6E (j : Fin 46632) : Fin 46656 :=
  ⟨min (xarr6E.getD j.1 0) 46655, by omega⟩

def endX6E (j : Fin 46632) : Fin 6 → Fin 6 := allMaps6 (xidx6E j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6E` is given. -/
def uidx6E : Fin 12 → Fin 24
  | 0 => 23
  | 1 => 9
  | 2 => 15
  | 3 => 1
  | 4 => 18
  | 5 => 4
  | 6 => 11
  | 7 => 21
  | 8 => 3
  | 9 => 13
  | 10 => 6
  | 11 => 16

theorem permE6E_eq_endE6E (i : Fin 12) : permE6E i = endE6E (uidx6E i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep6E : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6E : Fin 6 → Fin 6 → Fin 4 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (1, 1)
  | 0, 5 => (2, 1)
  | 1, 0 => (2, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 2)
  | 1, 3 => (2, 3)
  | 1, 4 => (3, 2)
  | 1, 5 => (1, 3)
  | 2, 0 => (1, 4)
  | 2, 1 => (2, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (1, 5)
  | 2, 4 => (2, 5)
  | 2, 5 => (3, 4)
  | 3, 0 => (3, 6)
  | 3, 1 => (1, 6)
  | 3, 2 => (2, 7)
  | 3, 3 => (0, 6)
  | 3, 4 => (1, 7)
  | 3, 5 => (2, 6)
  | 4, 0 => (2, 9)
  | 4, 1 => (3, 8)
  | 4, 2 => (1, 8)
  | 4, 3 => (2, 8)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 9)
  | 5, 0 => (1, 10)
  | 5, 1 => (2, 11)
  | 5, 2 => (3, 10)
  | 5, 3 => (1, 11)
  | 5, 4 => (2, 10)
  | 5, 5 => (0, 10)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6E0 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6E0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6E1 : Fin 1 → Fin 12
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6E2 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6E3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6E3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `4` orbit values named by the family's arguments. -/
def dec6E (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 4 → Fin 6
  | 0 => val6E0 a
  | 1 => b
  | 2 => c
  | 3 => val6E3 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6E_eq_transport`). -/
def tab6E (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6E0 a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => val6E3 d
  | 0, 4 => pE6E1 b
  | 0, 5 => pE6E1 c
  | 1, 0 => pE6E2 c
  | 1, 1 => pE6E2 (val6E0 a)
  | 1, 2 => pE6E2 b
  | 1, 3 => pE6E3 c
  | 1, 4 => pE6E2 (val6E3 d)
  | 1, 5 => pE6E3 b
  | 2, 0 => pE6E4 b
  | 2, 1 => pE6E4 c
  | 2, 2 => pE6E4 (val6E0 a)
  | 2, 3 => pE6E5 b
  | 2, 4 => pE6E5 c
  | 2, 5 => pE6E4 (val6E3 d)
  | 3, 0 => pE6E6 (val6E3 d)
  | 3, 1 => pE6E6 b
  | 3, 2 => pE6E7 c
  | 3, 3 => pE6E6 (val6E0 a)
  | 3, 4 => pE6E7 b
  | 3, 5 => pE6E6 c
  | 4, 0 => pE6E9 c
  | 4, 1 => pE6E8 (val6E3 d)
  | 4, 2 => pE6E8 b
  | 4, 3 => pE6E8 c
  | 4, 4 => pE6E8 (val6E0 a)
  | 4, 5 => pE6E9 b
  | 5, 0 => pE6E10 b
  | 5, 1 => pE6E11 c
  | 5, 2 => pE6E10 (val6E3 d)
  | 5, 3 => pE6E11 b
  | 5, 4 => pE6E10 c
  | 5, 5 => pE6E10 (val6E0 a)

theorem tab6E_eq_transport (a : Fin 2) (b c : Fin 6) (d : Fin 2) :
    tab6E a b c d = Magma.transport permE6E tr6E (dec6E a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `144` invariant tuples these are the ones the forbidden maps rule out; naming only them keeps
the exactness test off the hot path of a family scan. -/
def mem6E : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6E 1 2 1 0
  | 1 => tab6E 1 2 1 1
  | 2 => tab6E 1 5 4 0
  | 3 => tab6E 1 5 4 1

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6E` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6E : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr6E` is addressed. -/
def encT6E (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Nat :=
  a.1 * 72 +
    b.1 * 12 +
    c.1 * 2 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6E (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 4 :=
  ⟨min (rankArr6E.getD (encT6E a b c d) 0) 3, by omega⟩


/-- `2` of the `46632` forbidden maps, enough to separate the `4` members from the other `140`
invariant tuples on their own. The certificate still forbids all `46632`; this is the list
`mem_rank6E` scans, and scanning is quadratic. -/
def x0idx6E : Fin 2 → Fin 46632
  | 0 => 0
  | 1 => 1865

def endX06E (j : Fin 2) : Fin 6 → Fin 6 := endX6E (x0idx6E j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6E (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6E i)

theorem end6E_isEndo (i : Fin 4) (j : Fin 24) : (end6E i).IsEndo (endE6E j) := by
  revert i j; native_decide

theorem end6E_not_isEndo (i : Fin 4) (j : Fin 46632) : ¬ (end6E i).IsEndo (endX6E j) := by
  revert i j; native_decide

/-- `rank6E` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6E` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6E (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tab6E a b c d) endE6E endX06E = true) :
    mem6E (rank6E a b c d) = tab6E a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6E (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tab6E a b c d) endE6E endX06E = true) :
    ∃ i, mem6E i = tab6E a b c d :=
  ⟨_, mem_rank6E a b c d h⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6E`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6E` turns that into a member index. -/
theorem exists_end6E {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6E j))
    (hX : ∀ j, ¬ M.IsEndo (endX6E j)) : ∃ i, end6E i = M := by
  have hP : ∀ i, M.IsEndo (permE6E i) := by
    intro i; rw [permE6E_eq_endE6E]; exact hE (uidx6E i)
  have hop : M.op = Magma.transport permE6E tr6E (fun i ↦ M.op (rep6E i).1 (rep6E i).2) :=
    Magma.op_eq_transport (rep := rep6E) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6E) (idx := stabIdx6E0) (a := (rep6E 0).1) (b := (rep6E 0).2)
    (val := val6E0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6E) (idx := stabIdx6E1) (a := (rep6E 1).1) (b := (rep6E 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6E) (idx := stabIdx6E2) (a := (rep6E 2).1) (b := (rep6E 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6E) (idx := stabIdx6E3) (a := (rep6E 3).1) (b := (rep6E 3).2)
    (val := val6E3) hP (by decide) (by decide)
  have hdec : dec6E a b c d = fun i ↦ M.op (rep6E i).1 (rep6E i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab6E a b c d = M.op := by
    rw [tab6E_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6E a b c d) endE6E endX06E = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, fun j ↦ hX (x0idx6E j)⟩
  obtain ⟨i, hi⟩ := mem_of_isExact6E a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`24` monoid of `Magma.endE6E`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6E {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6E i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6E j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6E i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6E
    (fun k ↦ (Magma.end6E_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6E_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
