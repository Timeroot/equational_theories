import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `B` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `20`: `⟨(1 2 3 4 5), (2 3 5 4)⟩`

`End(M)` is `21` maps, so `Aut(M)` -- its unit group -- is these `20` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `5` orbit values rather than `36`
independent cells. -/

/-- The `20` elements of the group: `()`, `(2 3 5 4)`, `(2 4 5 3)`, `(2 5)(3 4)`, `(1 2)(3 5)`, `(1
2 3 4 5)`, `(1 2 4 3)`, `(1 2 5 4)`, `(1 3 4 2)`, `(1 3)(4 5)`, `(1 3 5 2 4)`, `(1 3 2 5)`, `(1 4 5
2)`, `(1 4 3 5)`, `(1 4)(2 3)`, `(1 4 2 5 3)`, `(1 5 4 3 2)`, `(1 5 3 4)`, `(1 5 2 3)`, `(1 5)(2
4)`. -/
def pE6B0 : Fin 6 → Fin 6 := id
def pE6B1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 2 | 5 => 4
def pE6B2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 5 | 5 => 3
def pE6B3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2
def pE6B4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
def pE6B5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 1
def pE6B6 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5
def pE6B7 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 4
def pE6B8 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5
def pE6B9 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4
def pE6B10 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 2
def pE6B11 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 4 | 5 => 1
def pE6B12 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 2
def pE6B13 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 3 | 5 => 1
def pE6B14 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5
def pE6B15 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 2 | 5 => 3
def pE6B16 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4
def pE6B17 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 3
def pE6B18 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 2
def pE6B19 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1

def permE6B : Fin 20 → Fin 6 → Fin 6
  | 0 => pE6B0
  | 1 => pE6B1
  | 2 => pE6B2
  | 3 => pE6B3
  | 4 => pE6B4
  | 5 => pE6B5
  | 6 => pE6B6
  | 7 => pE6B7
  | 8 => pE6B8
  | 9 => pE6B9
  | 10 => pE6B10
  | 11 => pE6B11
  | 12 => pE6B12
  | 13 => pE6B13
  | 14 => pE6B14
  | 15 => pE6B15
  | 16 => pE6B16
  | 17 => pE6B17
  | 18 => pE6B18
  | _ => pE6B19

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `21` self-maps that must be endomorphisms: `000000`, `054321`, `042531`,
`035241`, `023451`, `034512`, `015432`, `053142`, `041352`, `052413`, `045123`, `021543`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6B : Fin 21 → Fin 46656
  | 0 => 0
  | 1 => 11190
  | 2 => 12840
  | 3 => 13590
  | 4 => 15240
  | 5 => 18090
  | 6 => 20490
  | 7 => 21090
  | 8 => 22740
  | 9 => 25590
  | 10 => 26340
  | 11 => 29640
  | 12 => 30390
  | 13 => 33240
  | 14 => 34890
  | 15 => 35490
  | 16 => 37890
  | 17 => 40740
  | 18 => 42390
  | 19 => 43140
  | _ => 44790

def endE6B (j : Fin 21) : Fin 6 → Fin 6 := allMaps6 (eidx6B j)

/-- Indices of the other `46635`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6B : Array Nat := #[
  0, 11190, 12840, 13590, 15240, 18090, 20490, 21090, 22740, 25590, 26340, 29640, 30390, 33240,
  34890, 35490, 37890, 40740, 42390, 43140, 44790]

def xarr6B : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6B.contains i)

def xidx6B (j : Fin 46635) : Fin 46656 :=
  ⟨min (xarr6B.getD j.1 0) 46655, by omega⟩

def endX6B (j : Fin 46635) : Fin 6 → Fin 6 := allMaps6 (xidx6B j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6B` is given. -/
def uidx6B : Fin 20 → Fin 21
  | 0 => 20
  | 1 => 14
  | 2 => 12
  | 3 => 6
  | 4 => 11
  | 5 => 4
  | 6 => 19
  | 7 => 13
  | 8 => 18
  | 9 => 16
  | 10 => 5
  | 11 => 3
  | 12 => 8
  | 13 => 2
  | 14 => 17
  | 15 => 10
  | 16 => 15
  | 17 => 9
  | 18 => 7
  | _ => 1

theorem permE6B_eq_endE6B (i : Fin 20) : permE6B i = endE6B (uidx6B i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `5`, so an invariant
operation is `5` values. -/
def rep6B : Fin 5 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6B : Fin 6 → Fin 6 → Fin 5 × Fin 20
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
def stabIdx6B0 : Fin 20 → Fin 20
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
def val6B0 : Fin 1 → Fin 6
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6B1 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6B1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6B2 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6B2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6B3 : Fin 4 → Fin 20
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6B3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6B4 : Fin 1 → Fin 20
  | 0 => 0

/-- The `5` orbit values named by the family's arguments. -/
def dec6B (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Fin 5 → Fin 6
  | 0 => val6B0 a
  | 1 => val6B1 b
  | 2 => val6B2 c
  | 3 => val6B3 d
  | 4 => e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6B_eq_transport`). -/
def tab6B (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6B0 a
  | 0, 1 => val6B1 b
  | 0, 2 => pE6B4 (val6B1 b)
  | 0, 3 => pE6B8 (val6B1 b)
  | 0, 4 => pE6B12 (val6B1 b)
  | 0, 5 => pE6B16 (val6B1 b)
  | 1, 0 => val6B2 c
  | 1, 1 => val6B3 d
  | 1, 2 => e
  | 1, 3 => pE6B1 e
  | 1, 4 => pE6B2 e
  | 1, 5 => pE6B3 e
  | 2, 0 => pE6B4 (val6B2 c)
  | 2, 1 => pE6B4 e
  | 2, 2 => pE6B4 (val6B3 d)
  | 2, 3 => pE6B5 e
  | 2, 4 => pE6B6 e
  | 2, 5 => pE6B7 e
  | 3, 0 => pE6B8 (val6B2 c)
  | 3, 1 => pE6B8 e
  | 3, 2 => pE6B9 e
  | 3, 3 => pE6B8 (val6B3 d)
  | 3, 4 => pE6B10 e
  | 3, 5 => pE6B11 e
  | 4, 0 => pE6B12 (val6B2 c)
  | 4, 1 => pE6B12 e
  | 4, 2 => pE6B13 e
  | 4, 3 => pE6B14 e
  | 4, 4 => pE6B12 (val6B3 d)
  | 4, 5 => pE6B15 e
  | 5, 0 => pE6B16 (val6B2 c)
  | 5, 1 => pE6B16 e
  | 5, 2 => pE6B17 e
  | 5, 3 => pE6B18 e
  | 5, 4 => pE6B19 e
  | 5, 5 => pE6B16 (val6B3 d)

theorem tab6B_eq_transport (a : Fin 1) (b c d : Fin 2) (e : Fin 6) :
    tab6B a b c d e = Magma.transport permE6B tr6B (dec6B a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `12` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `48` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6B : Fin 12 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6B 0 0 0 0 3
  | 1 => tab6B 0 0 0 0 4
  | 2 => tab6B 0 0 0 0 5
  | 3 => tab6B 0 0 1 0 3
  | 4 => tab6B 0 0 1 0 4
  | 5 => tab6B 0 0 1 0 5
  | 6 => tab6B 0 1 0 0 3
  | 7 => tab6B 0 1 0 0 4
  | 8 => tab6B 0 1 0 0 5
  | 9 => tab6B 0 1 1 0 3
  | 10 => tab6B 0 1 1 0 4
  | 11 => tab6B 0 1 1 0 5

/-- Which of the `12` members a given invariant tuple is, so that `mem_of_isExact6B` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6B : Array Nat := #[
  0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 7, 8, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 9, 10, 11, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr6B` is addressed. -/
def encT6B (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Nat :=
  a.1 * 48 +
    b.1 * 24 +
    c.1 * 12 +
    d.1 * 6 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6B (a : Fin 1) (b c d : Fin 2) (e : Fin 6) : Fin 12 :=
  ⟨min (rankArr6B.getD (encT6B a b c d e) 0) 11, by omega⟩


/-- `2` of the `46635` forbidden maps, enough to separate the `12` members from the other `36`
invariant tuples on their own. The certificate still forbids all `46635`; this is the list
`mem_rank6B` scans, and scanning is quadratic. -/
def x0idx6B : Fin 2 → Fin 46635
  | 0 => 9329
  | 1 => 11218

def endX06B (j : Fin 2) : Fin 6 → Fin 6 := endX6B (x0idx6B j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6B (i : Fin 12) : Magma (Fin 6) := Magma.mk (mem6B i)

theorem end6B_isEndo (i : Fin 12) (j : Fin 21) : (end6B i).IsEndo (endE6B j) := by
  revert i j; native_decide

theorem end6B_not_isEndo (i : Fin 12) (j : Fin 46635) : ¬ (end6B i).IsEndo (endX6B j) := by
  revert i j; native_decide

/-- `rank6B` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6B` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6B (a : Fin 1) (b c d : Fin 2) (e : Fin 6)
    (h : Magma.isExact (tab6B a b c d e) endE6B endX06B = true) :
    mem6B (rank6B a b c d e) = tab6B a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `12` listed
members. -/
theorem mem_of_isExact6B (a : Fin 1) (b c d : Fin 2) (e : Fin 6)
    (h : Magma.isExact (tab6B a b c d e) endE6B endX06B = true) :
    ∃ i, mem6B i = tab6B a b c d e :=
  ⟨_, mem_rank6B a b c d e h⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6B`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6B` turns that into a member index. -/
theorem exists_end6B {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6B j))
    (hX : ∀ j, ¬ M.IsEndo (endX6B j)) : ∃ i, end6B i = M := by
  have hP : ∀ i, M.IsEndo (permE6B i) := by
    intro i; rw [permE6B_eq_endE6B]; exact hE (uidx6B i)
  have hop : M.op = Magma.transport permE6B tr6B (fun i ↦ M.op (rep6B i).1 (rep6B i).2) :=
    Magma.op_eq_transport (rep := rep6B) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6B) (idx := stabIdx6B0) (a := (rep6B 0).1) (b := (rep6B 0).2)
    (val := val6B0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6B) (idx := stabIdx6B1) (a := (rep6B 1).1) (b := (rep6B 1).2)
    (val := val6B1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6B) (idx := stabIdx6B2) (a := (rep6B 2).1) (b := (rep6B 2).2)
    (val := val6B2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6B) (idx := stabIdx6B3) (a := (rep6B 3).1) (b := (rep6B 3).2)
    (val := val6B3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6B) (idx := stabIdx6B4) (a := (rep6B 4).1) (b := (rep6B 4).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6B a b c d e = fun i ↦ M.op (rep6B i).1 (rep6B i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tab6B a b c d e = M.op := by
    rw [tab6B_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6B a b c d e) endE6B endX06B = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, fun j ↦ hX (x0idx6B j)⟩
  obtain ⟨i, hi⟩ := mem_of_isExact6B a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`21` monoid of `Magma.endE6B`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6B {L L' : Law.NatMagmaLaw} {i : Fin 12}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6B i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6B j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6B i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6B
    (fun k ↦ (Magma.end6B_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6B_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
