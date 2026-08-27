import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `C` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(2 3)(4 5), (0 1 2 4 5 3)⟩`

`End(M)` is `18` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(1 3)(2 5)`, `(0 1)(2 3)(4 5)`, `(0 1 2 4 5 3)`, `(0 2)(3
4)`, `(0 2 5)(1 4 3)`, `(0 3 5 4 2 1)`, `(0 3)(1 5)(2 4)`, `(0 4)(1 2)(3 5)`, `(0 4)(1 5)(2 3)`, `(0
5 2)(1 3 4)`, `(0 5)(1 4)`. -/
def pE6C0 : Fin 6 → Fin 6 := id
def pE6C1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 2
def pE6C2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6C3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 3
def pE6C4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5
def pE6C5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 0
def pE6C6 : Fin 6 → Fin 6 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 4
def pE6C7 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 1
def pE6C8 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 0 | 5 => 3
def pE6C9 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 1
def pE6C10 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 2
def pE6C11 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 0

def permE6C : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6C0
  | 1 => pE6C1
  | 2 => pE6C2
  | 3 => pE6C3
  | 4 => pE6C4
  | 5 => pE6C5
  | 6 => pE6C6
  | 7 => pE6C7
  | 8 => pE6C8
  | 9 => pE6C9
  | 10 => pE6C10
  | 11 => pE6C11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `18` self-maps that must be endomorphisms: `542310`, `245130`, `040440`,
`453201`, `354021`, `151551`, `530412`, `232332`, `035142`, `421503`, `323223`, `124053`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6C : Fin 18 → Fin 46656
  | 0 => 2045
  | 1 => 4310
  | 2 => 6072
  | 3 => 8350
  | 4 => 10545
  | 5 => 15403
  | 6 => 17735
  | 7 => 20180
  | 8 => 21150
  | 9 => 24460
  | 10 => 26475
  | 11 => 29965
  | 12 => 31252
  | 13 => 34815
  | 14 => 38125
  | 15 => 40583
  | 16 => 43640
  | _ => 44790

def endE6C (j : Fin 18) : Fin 6 → Fin 6 := allMaps6 (eidx6C j)

/-- Indices of the other `46638`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6C : Array Nat := #[
  2045, 4310, 6072, 8350, 10545, 15403, 17735, 20180, 21150, 24460, 26475, 29965, 31252, 34815,
  38125, 40583, 43640, 44790]

def xarr6C : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6C.contains i)

def xidx6C (j : Fin 46638) : Fin 46656 :=
  ⟨min (xarr6C.getD j.1 0) 46655, by omega⟩

def endX6C (j : Fin 46638) : Fin 6 → Fin 6 := allMaps6 (xidx6C j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6C` is given. -/
def uidx6C : Fin 12 → Fin 18
  | 0 => 17
  | 1 => 8
  | 2 => 14
  | 3 => 11
  | 4 => 16
  | 5 => 1
  | 6 => 13
  | 7 => 4
  | 8 => 9
  | 9 => 3
  | 10 => 6
  | 11 => 0

theorem permE6C_eq_endE6C (i : Fin 12) : permE6C i = endE6C (uidx6C i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep6C : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6C : Fin 6 → Fin 6 → Fin 4 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (1, 1)
  | 0, 4 => (3, 0)
  | 0, 5 => (2, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 3)
  | 1, 3 => (2, 2)
  | 1, 4 => (2, 3)
  | 1, 5 => (3, 2)
  | 2, 0 => (2, 4)
  | 2, 1 => (1, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 4)
  | 2, 4 => (1, 5)
  | 2, 5 => (2, 5)
  | 3, 0 => (1, 6)
  | 3, 1 => (2, 6)
  | 3, 2 => (3, 6)
  | 3, 3 => (0, 6)
  | 3, 4 => (2, 7)
  | 3, 5 => (1, 7)
  | 4, 0 => (3, 8)
  | 4, 1 => (2, 8)
  | 4, 2 => (1, 8)
  | 4, 3 => (2, 9)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 9)
  | 5, 0 => (2, 10)
  | 5, 1 => (3, 10)
  | 5, 2 => (2, 11)
  | 5, 3 => (1, 10)
  | 5, 4 => (1, 11)
  | 5, 5 => (0, 10)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6C0 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6C0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 4

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6C1 : Fin 1 → Fin 12
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6C2 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6C3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6C3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 4

/-- The `4` orbit values named by the family's arguments. -/
def dec6C (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 4 → Fin 6
  | 0 => val6C0 a
  | 1 => b
  | 2 => c
  | 3 => val6C3 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6C_eq_transport`). -/
def tab6C (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6C0 a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => pE6C1 b
  | 0, 4 => val6C3 d
  | 0, 5 => pE6C1 c
  | 1, 0 => pE6C2 b
  | 1, 1 => pE6C2 (val6C0 a)
  | 1, 2 => pE6C3 b
  | 1, 3 => pE6C2 c
  | 1, 4 => pE6C3 c
  | 1, 5 => pE6C2 (val6C3 d)
  | 2, 0 => pE6C4 c
  | 2, 1 => pE6C4 b
  | 2, 2 => pE6C4 (val6C0 a)
  | 2, 3 => pE6C4 (val6C3 d)
  | 2, 4 => pE6C5 b
  | 2, 5 => pE6C5 c
  | 3, 0 => pE6C6 b
  | 3, 1 => pE6C6 c
  | 3, 2 => pE6C6 (val6C3 d)
  | 3, 3 => pE6C6 (val6C0 a)
  | 3, 4 => pE6C7 c
  | 3, 5 => pE6C7 b
  | 4, 0 => pE6C8 (val6C3 d)
  | 4, 1 => pE6C8 c
  | 4, 2 => pE6C8 b
  | 4, 3 => pE6C9 c
  | 4, 4 => pE6C8 (val6C0 a)
  | 4, 5 => pE6C9 b
  | 5, 0 => pE6C10 c
  | 5, 1 => pE6C10 (val6C3 d)
  | 5, 2 => pE6C11 c
  | 5, 3 => pE6C10 b
  | 5, 4 => pE6C11 b
  | 5, 5 => pE6C10 (val6C0 a)

theorem tab6C_eq_transport (a : Fin 2) (b c : Fin 6) (d : Fin 2) :
    tab6C a b c d = Magma.transport permE6C tr6C (dec6C a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `10` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `144` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6C : Fin 10 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6C 1 0 1 0
  | 1 => tab6C 1 1 1 1
  | 2 => tab6C 1 2 1 0
  | 3 => tab6C 1 2 3 0
  | 4 => tab6C 1 2 4 0
  | 5 => tab6C 1 3 1 1
  | 6 => tab6C 1 3 3 1
  | 7 => tab6C 1 3 4 1
  | 8 => tab6C 1 4 1 1
  | 9 => tab6C 1 5 1 0

/-- Which of the `10` members a given invariant tuple is, so that `mem_of_isExact6C` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6C : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 2, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 6, 0, 7, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr6C` is addressed. -/
def encT6C (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Nat :=
  a.1 * 72 +
    b.1 * 12 +
    c.1 * 2 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6C (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 10 :=
  ⟨min (rankArr6C.getD (encT6C a b c d) 0) 9, by omega⟩


/-- `2` of the `46638` forbidden maps, enough to separate the `10` members from the other `134`
invariant tuples on their own. The certificate still forbids all `46638`; this is the list
`mem_rank6C` scans, and scanning is quadratic. -/
def x0idx6C : Fin 2 → Fin 46638
  | 0 => 0
  | 1 => 1721

def endX06C (j : Fin 2) : Fin 6 → Fin 6 := endX6C (x0idx6C j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6C (i : Fin 10) : Magma (Fin 6) := Magma.mk (mem6C i)

theorem end6C_isEndo (i : Fin 10) (j : Fin 18) : (end6C i).IsEndo (endE6C j) := by
  revert i j; native_decide

theorem end6C_not_isEndo (i : Fin 10) (j : Fin 46638) : ¬ (end6C i).IsEndo (endX6C j) := by
  revert i j; native_decide

/-- `rank6C` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6C` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6C (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tab6C a b c d) endE6C endX06C = true) :
    mem6C (rank6C a b c d) = tab6C a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `10` listed
members. -/
theorem mem_of_isExact6C (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tab6C a b c d) endE6C endX06C = true) :
    ∃ i, mem6C i = tab6C a b c d :=
  ⟨_, mem_rank6C a b c d h⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6C`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6C` turns that into a member index. -/
theorem exists_end6C {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6C j))
    (hX : ∀ j, ¬ M.IsEndo (endX6C j)) : ∃ i, end6C i = M := by
  have hP : ∀ i, M.IsEndo (permE6C i) := by
    intro i; rw [permE6C_eq_endE6C]; exact hE (uidx6C i)
  have hop : M.op = Magma.transport permE6C tr6C (fun i ↦ M.op (rep6C i).1 (rep6C i).2) :=
    Magma.op_eq_transport (rep := rep6C) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6C) (idx := stabIdx6C0) (a := (rep6C 0).1) (b := (rep6C 0).2)
    (val := val6C0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6C) (idx := stabIdx6C1) (a := (rep6C 1).1) (b := (rep6C 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6C) (idx := stabIdx6C2) (a := (rep6C 2).1) (b := (rep6C 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6C) (idx := stabIdx6C3) (a := (rep6C 3).1) (b := (rep6C 3).2)
    (val := val6C3) hP (by decide) (by decide)
  have hdec : dec6C a b c d = fun i ↦ M.op (rep6C i).1 (rep6C i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab6C a b c d = M.op := by
    rw [tab6C_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6C a b c d) endE6C endX06C = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, fun j ↦ hX (x0idx6C j)⟩
  obtain ⟨i, hi⟩ := mem_of_isExact6C a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`18` monoid of `Magma.endE6C`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6C {L L' : Law.NatMagmaLaw} {i : Fin 10}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6C i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6C j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6C i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6C
    (fun k ↦ (Magma.end6C_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6C_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
