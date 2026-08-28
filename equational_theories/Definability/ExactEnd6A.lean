import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `A` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `18`: `⟨(0 1)(2 3)(4 5), (0 1 3 2 5 4)⟩`

`End(M)` is `36` maps, so `Aut(M)` -- its unit group -- is these `18` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `36`
independent cells. -/

/-- The `18` elements of the group: `()`, `(1 2 4)`, `(1 4 2)`, `(0 1)(2 3)(4 5)`, `(0 1 3 2 5 4)`,
`(0 1 5 4 3 2)`, `(0 2 3 4 5 1)`, `(0 2 5 1 3 4)`, `(0 2)(1 5)(3 4)`, `(0 3 5)`, `(0 3 5)(1 2 4)`,
`(0 3 5)(1 4 2)`, `(0 4 5 2 3 1)`, `(0 4)(1 3)(2 5)`, `(0 4 3 1 5 2)`, `(0 5 3)`, `(0 5 3)(1 2 4)`,
`(0 5 3)(1 4 2)`. -/
def pE6A0 : Fin 6 → Fin 6 := id
def pE6A1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5
def pE6A2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5
def pE6A3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6A4 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 4
def pE6A5 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 4
def pE6A6 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 1
def pE6A7 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 1
def pE6A8 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1
def pE6A9 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 0
def pE6A10 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 0
def pE6A11 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 0
def pE6A12 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 2
def pE6A13 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 0 | 5 => 2
def pE6A14 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 2
def pE6A15 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 3
def pE6A16 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 3
def pE6A17 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 3

def permE6A : Fin 18 → Fin 6 → Fin 6
  | 0 => pE6A0
  | 1 => pE6A1
  | 2 => pE6A2
  | 3 => pE6A3
  | 4 => pE6A4
  | 5 => pE6A5
  | 6 => pE6A6
  | 7 => pE6A7
  | 8 => pE6A8
  | 9 => pE6A9
  | 10 => pE6A10
  | 11 => pE6A11
  | 12 => pE6A12
  | 13 => pE6A13
  | 14 => pE6A14
  | 15 => pE6A15
  | 16 => pE6A16
  | _ => pE6A17

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `36` self-maps that must be endomorphisms: `335500`, `324510`, `341520`,
`350530`, `312540`, `303550`, `235401`, `224411`, `241421`, `250431`, `212441`, `203451`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6A : Fin 36 → Fin 46656
  | 0 => 1281
  | 1 => 2535
  | 2 => 3735
  | 3 => 5001
  | 4 => 6345
  | 5 => 7671
  | 6 => 8840
  | 7 => 10094
  | 8 => 11294
  | 9 => 12560
  | 10 => 13904
  | 11 => 15230
  | 12 => 15970
  | 13 => 17224
  | 14 => 18424
  | 15 => 19690
  | 16 => 21034
  | 17 => 22360
  | 18 => 23531
  | 19 => 24785
  | 20 => 25985
  | 21 => 27251
  | 22 => 28595
  | 23 => 29921
  | 24 => 31735
  | 25 => 32989
  | 26 => 34189
  | 27 => 35455
  | 28 => 36799
  | 29 => 38125
  | 30 => 39726
  | 31 => 40980
  | 32 => 42180
  | 33 => 43446
  | 34 => 44790
  | _ => 46116

def endE6A (j : Fin 36) : Fin 6 → Fin 6 := allMaps6 (eidx6A j)

/-- Indices of the other `46620`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6A : Array Nat := #[
  1281, 2535, 3735, 5001, 6345, 7671, 8840, 10094, 11294, 12560, 13904, 15230, 15970, 17224,
  18424, 19690, 21034, 22360, 23531, 24785, 25985, 27251, 28595, 29921, 31735, 32989, 34189,
  35455, 36799, 38125, 39726, 40980, 42180, 43446, 44790, 46116]

def xarr6A : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6A.contains i)

def xidx6A (j : Fin 46620) : Fin 46656 :=
  ⟨min (xarr6A.getD j.1 0) 46655, by omega⟩

def endX6A (j : Fin 46620) : Fin 6 → Fin 6 := allMaps6 (xidx6A j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6A` is given. -/
def uidx6A : Fin 18 → Fin 36
  | 0 => 34
  | 1 => 31
  | 2 => 32
  | 3 => 29
  | 4 => 24
  | 5 => 27
  | 6 => 11
  | 7 => 6
  | 8 => 9
  | 9 => 4
  | 10 => 1
  | 11 => 2
  | 12 => 17
  | 13 => 12
  | 14 => 15
  | 15 => 22
  | 16 => 19
  | _ => 20

theorem permE6A_eq_endE6A (i : Fin 18) : permE6A i = endE6A (uidx6A i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep6A : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6A : Fin 6 → Fin 6 → Fin 4 × Fin 18
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (1, 2)
  | 0, 5 => (3, 0)
  | 1, 0 => (1, 3)
  | 1, 1 => (0, 3)
  | 1, 2 => (2, 3)
  | 1, 3 => (1, 4)
  | 1, 4 => (3, 3)
  | 1, 5 => (1, 5)
  | 2, 0 => (1, 6)
  | 2, 1 => (3, 6)
  | 2, 2 => (0, 6)
  | 2, 3 => (1, 7)
  | 2, 4 => (2, 6)
  | 2, 5 => (1, 8)
  | 3, 0 => (3, 9)
  | 3, 1 => (1, 9)
  | 3, 2 => (1, 10)
  | 3, 3 => (0, 9)
  | 3, 4 => (1, 11)
  | 3, 5 => (2, 9)
  | 4, 0 => (1, 12)
  | 4, 1 => (2, 12)
  | 4, 2 => (3, 12)
  | 4, 3 => (1, 13)
  | 4, 4 => (0, 12)
  | 4, 5 => (1, 14)
  | 5, 0 => (2, 15)
  | 5, 1 => (1, 15)
  | 5, 2 => (1, 16)
  | 5, 3 => (3, 15)
  | 5, 4 => (1, 17)
  | 5, 5 => (0, 15)

/-- The `3` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6A0 : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 1
  | 2 => 2
def val6A0 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6A1 : Fin 1 → Fin 18
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6A2 : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 1
  | 2 => 2
def val6A2 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6A3 : Fin 3 → Fin 18
  | 0 => 0
  | 1 => 1
  | 2 => 2
def val6A3 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The `4` orbit values named by the family's arguments. -/
def dec6A (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Fin 4 → Fin 6
  | 0 => val6A0 a
  | 1 => b
  | 2 => val6A2 c
  | 3 => val6A3 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6A_eq_transport`). -/
def tab6A (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6A0 a
  | 0, 1 => b
  | 0, 2 => pE6A1 b
  | 0, 3 => val6A2 c
  | 0, 4 => pE6A2 b
  | 0, 5 => val6A3 d
  | 1, 0 => pE6A3 b
  | 1, 1 => pE6A3 (val6A0 a)
  | 1, 2 => pE6A3 (val6A2 c)
  | 1, 3 => pE6A4 b
  | 1, 4 => pE6A3 (val6A3 d)
  | 1, 5 => pE6A5 b
  | 2, 0 => pE6A6 b
  | 2, 1 => pE6A6 (val6A3 d)
  | 2, 2 => pE6A6 (val6A0 a)
  | 2, 3 => pE6A7 b
  | 2, 4 => pE6A6 (val6A2 c)
  | 2, 5 => pE6A8 b
  | 3, 0 => pE6A9 (val6A3 d)
  | 3, 1 => pE6A9 b
  | 3, 2 => pE6A10 b
  | 3, 3 => pE6A9 (val6A0 a)
  | 3, 4 => pE6A11 b
  | 3, 5 => pE6A9 (val6A2 c)
  | 4, 0 => pE6A12 b
  | 4, 1 => pE6A12 (val6A2 c)
  | 4, 2 => pE6A12 (val6A3 d)
  | 4, 3 => pE6A13 b
  | 4, 4 => pE6A12 (val6A0 a)
  | 4, 5 => pE6A14 b
  | 5, 0 => pE6A15 (val6A2 c)
  | 5, 1 => pE6A15 b
  | 5, 2 => pE6A16 b
  | 5, 3 => pE6A15 (val6A3 d)
  | 5, 4 => pE6A17 b
  | 5, 5 => pE6A15 (val6A0 a)

theorem tab6A_eq_transport (a : Fin 3) (b : Fin 6) (c d : Fin 3) :
    tab6A a b c d = Magma.transport permE6A tr6A (dec6A a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `162` invariant tuples these are the ones the forbidden maps rule out; naming only them keeps
the exactness test off the hot path of a family scan. -/
def mem6A : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6A 1 2 2 0
  | 1 => tab6A 1 3 1 1
  | 2 => tab6A 2 4 0 1
  | 3 => tab6A 2 5 2 2

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6A` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6A : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 3]

/-- The arguments as one mixed-radix index, which is how `rankArr6A` is addressed. -/
def encT6A (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Nat :=
  a.1 * 54 +
    b.1 * 9 +
    c.1 * 3 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6A (a : Fin 3) (b : Fin 6) (c d : Fin 3) : Fin 4 :=
  ⟨min (rankArr6A.getD (encT6A a b c d) 0) 3, by omega⟩


/-- `1` of the `36` demanded maps and `1` of the `46620` forbidden ones, enough to separate the `4`
members from the other `158` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6A` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6A : Fin 1 → Fin 36
  | 0 => 0
def x0idx6A : Fin 1 → Fin 46620
  | 0 => 0

def endE06A (j : Fin 1) : Fin 6 → Fin 6 := endE6A (e0idx6A j)

def endX06A (j : Fin 1) : Fin 6 → Fin 6 := endX6A (x0idx6A j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6A (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6A i)

theorem end6A_isEndo (i : Fin 4) (j : Fin 36) : (end6A i).IsEndo (endE6A j) := by
  revert i j; native_decide

theorem end6A_not_isEndo (i : Fin 4) (j : Fin 46620) : ¬ (end6A i).IsEndo (endX6A j) := by
  revert i j; native_decide

/-- `rank6A` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6A` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6A (a : Fin 3) (b : Fin 6) (c d : Fin 3)
    (hx : Magma.isExact (tab6A a b c d) endE06A endX06A = true) :
    mem6A (rank6A a b c d) = tab6A a b c d := by
  revert hx; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6A (a : Fin 3) (b : Fin 6) (c d : Fin 3)
    (hx : Magma.isExact (tab6A a b c d) endE06A endX06A = true) :
    ∃ idx, mem6A idx = tab6A a b c d :=
  ⟨_, mem_rank6A a b c d hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6A`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6A` turns that into a member index. -/
theorem exists_end6A {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6A j))
    (hX : ∀ j, ¬ M.IsEndo (endX6A j)) : ∃ i, end6A i = M := by
  have hP : ∀ i, M.IsEndo (permE6A i) := by
    intro i; rw [permE6A_eq_endE6A]; exact hE (uidx6A i)
  have hop : M.op = Magma.transport permE6A tr6A (fun i ↦ M.op (rep6A i).1 (rep6A i).2) :=
    Magma.op_eq_transport (rep := rep6A) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6A) (idx := stabIdx6A0) (a := (rep6A 0).1) (b := (rep6A 0).2)
    (val := val6A0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6A) (idx := stabIdx6A1) (a := (rep6A 1).1) (b := (rep6A 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6A) (idx := stabIdx6A2) (a := (rep6A 2).1) (b := (rep6A 2).2)
    (val := val6A2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6A) (idx := stabIdx6A3) (a := (rep6A 3).1) (b := (rep6A 3).2)
    (val := val6A3) hP (by decide) (by decide)
  have hdec : dec6A a b c d = fun i ↦ M.op (rep6A i).1 (rep6A i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab6A a b c d = M.op := by
    rw [tab6A_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6A a b c d) endE06A endX06A = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6A j), fun j ↦ hX (x0idx6A j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6A a b c d hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`36` monoid of `Magma.endE6A`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6A {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6A i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6A j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6A i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6A
    (fun k ↦ (Magma.end6A_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6A_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
