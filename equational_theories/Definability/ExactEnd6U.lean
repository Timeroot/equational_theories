import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `U` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(2 3)(4 5), (0 2)(4 5)⟩`

`End(M)` is `18` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(2 3)(4 5)`, `(0 2)(4 5)`, `(0 2 3)`, `(0 3 2)`, `(0 3)(4
5)`. -/
def pE6U0 : Fin 6 → Fin 6 := id
def pE6U1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6U2 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pE6U3 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5
def pE6U4 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5
def pE6U5 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4

def permE6U : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6U0
  | 1 => pE6U1
  | 2 => pE6U2
  | 3 => pE6U3
  | 4 => pE6U4
  | 5 => pE6U5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `18` self-maps that must be endomorphisms: `010011`, `111111`, `212211`,
`313311`, `414411`, `514411`, `415411`, `515411`, `414511`, `514511`, `415511`, `515511`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6U : Fin 18 → Fin 46656
  | 0 => 9078
  | 1 => 9331
  | 2 => 9584
  | 3 => 9837
  | 4 => 10090
  | 5 => 10091
  | 6 => 10126
  | 7 => 10127
  | 8 => 10306
  | 9 => 10307
  | 10 => 10342
  | 11 => 10343
  | 12 => 37665
  | 13 => 38130
  | 14 => 38240
  | 15 => 44180
  | 16 => 44505
  | _ => 44790

def endE6U (j : Fin 18) : Fin 6 → Fin 6 := allMaps6 (eidx6U j)

/-- Indices of the other `46638`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6U : Array Nat := #[
  9078, 9331, 9584, 9837, 10090, 10091, 10126, 10127, 10306, 10307, 10342, 10343, 37665, 38130,
  38240, 44180, 44505, 44790]

def xarr6U : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6U.contains i)

def xidx6U (j : Fin 46638) : Fin 46656 :=
  ⟨min (xarr6U.getD j.1 0) 46655, by omega⟩

def endX6U (j : Fin 46638) : Fin 6 → Fin 6 := allMaps6 (xidx6U j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6U` is given. -/
def uidx6U : Fin 6 → Fin 18
  | 0 => 17
  | 1 => 13
  | 2 => 14
  | 3 => 15
  | 4 => 16
  | 5 => 12

theorem permE6U_eq_endE6U (i : Fin 6) : permE6U i = endE6U (uidx6U i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6U : Fin 11 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (1, 0)
  | 5 => (1, 1)
  | 6 => (1, 4)
  | 7 => (4, 0)
  | 8 => (4, 1)
  | 9 => (4, 4)
  | 10 => (4, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6U : Fin 6 → Fin 6 → Fin 11 × Fin 6
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (4, 0)
  | 1, 1 => (5, 0)
  | 1, 2 => (4, 2)
  | 1, 3 => (4, 4)
  | 1, 4 => (6, 0)
  | 1, 5 => (6, 1)
  | 2, 0 => (2, 2)
  | 2, 1 => (1, 2)
  | 2, 2 => (0, 2)
  | 2, 3 => (2, 3)
  | 2, 4 => (3, 3)
  | 2, 5 => (3, 2)
  | 3, 0 => (2, 4)
  | 3, 1 => (1, 4)
  | 3, 2 => (2, 5)
  | 3, 3 => (0, 4)
  | 3, 4 => (3, 4)
  | 3, 5 => (3, 5)
  | 4, 0 => (7, 0)
  | 4, 1 => (8, 0)
  | 4, 2 => (7, 3)
  | 4, 3 => (7, 4)
  | 4, 4 => (9, 0)
  | 4, 5 => (10, 0)
  | 5, 0 => (7, 1)
  | 5, 1 => (8, 1)
  | 5, 2 => (7, 2)
  | 5, 3 => (7, 5)
  | 5, 4 => (10, 1)
  | 5, 5 => (9, 1)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6U0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6U0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6U1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6U1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6U2 : Fin 1 → Fin 6
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6U3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6U4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6U4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `1`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6U5 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6U5 : Fin 1 → Fin 6
  | 0 => 1

/-- The `3` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6U6 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6U6 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6U7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6U8 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6U8 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6U9 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6U9 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6U10 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6U10 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6U (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 11 → Fin 6
  | 0 => val6U0 a
  | 1 => val6U1 b
  | 2 => c
  | 3 => d
  | 4 => val6U4 e
  | 5 => val6U5 f
  | 6 => val6U6 g
  | 7 => h
  | 8 => val6U8 i
  | 9 => val6U9 j
  | 10 => val6U10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6U_eq_transport`). -/
def tab6U (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6U0 a
  | 0, 1 => val6U1 b
  | 0, 2 => c
  | 0, 3 => pE6U1 c
  | 0, 4 => d
  | 0, 5 => pE6U1 d
  | 1, 0 => val6U4 e
  | 1, 1 => val6U5 f
  | 1, 2 => pE6U2 (val6U4 e)
  | 1, 3 => pE6U4 (val6U4 e)
  | 1, 4 => val6U6 g
  | 1, 5 => pE6U1 (val6U6 g)
  | 2, 0 => pE6U2 c
  | 2, 1 => pE6U2 (val6U1 b)
  | 2, 2 => pE6U2 (val6U0 a)
  | 2, 3 => pE6U3 c
  | 2, 4 => pE6U3 d
  | 2, 5 => pE6U2 d
  | 3, 0 => pE6U4 c
  | 3, 1 => pE6U4 (val6U1 b)
  | 3, 2 => pE6U5 c
  | 3, 3 => pE6U4 (val6U0 a)
  | 3, 4 => pE6U4 d
  | 3, 5 => pE6U5 d
  | 4, 0 => h
  | 4, 1 => val6U8 i
  | 4, 2 => pE6U3 h
  | 4, 3 => pE6U4 h
  | 4, 4 => val6U9 j
  | 4, 5 => val6U10 k
  | 5, 0 => pE6U1 h
  | 5, 1 => pE6U1 (val6U8 i)
  | 5, 2 => pE6U2 h
  | 5, 3 => pE6U5 h
  | 5, 4 => pE6U1 (val6U10 k)
  | 5, 5 => pE6U1 (val6U9 j)

theorem tab6U_eq_transport (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3)
    (h : Fin 6) (i j k : Fin 3) :
    tab6U a b c d e f g h i j k = Magma.transport permE6U tr6U (dec6U a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `14` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `139968` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6U : Fin 14 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6U 1 0 4 0 0 0 1 0 1 0 0
  | 1 => tab6U 1 0 4 0 1 0 0 1 1 0 0
  | 2 => tab6U 1 0 4 0 1 0 0 4 1 0 0
  | 3 => tab6U 1 0 4 0 1 0 0 5 1 0 0
  | 4 => tab6U 1 0 5 0 0 0 1 0 1 0 0
  | 5 => tab6U 1 0 5 0 1 0 0 1 1 0 0
  | 6 => tab6U 1 0 5 0 1 0 0 4 1 0 0
  | 7 => tab6U 1 0 5 0 1 0 0 5 1 0 0
  | 8 => tab6U 1 1 4 1 0 0 1 0 0 0 0
  | 9 => tab6U 1 1 4 4 0 0 1 0 0 0 0
  | 10 => tab6U 1 1 4 5 0 0 1 0 0 0 0
  | 11 => tab6U 1 1 5 1 0 0 1 0 0 0 0
  | 12 => tab6U 1 1 5 4 0 0 1 0 0 0 0
  | 13 => tab6U 1 1 5 5 0 0 1 0 0 0 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6U` is addressed. -/
def encT6U (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Nat :=
  a.1 * 69984 +
    b.1 * 34992 +
    c.1 * 5832 +
    d.1 * 972 +
    e.1 * 486 +
    f.1 * 486 +
    g.1 * 162 +
    h.1 * 27 +
    i.1 * 9 +
    j.1 * 3 +
    k.1

/-- Which of the `14` members a given invariant tuple is, so that `mem_of_isExact6U` can name one
rather than search the list for it. The `139954` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6U` excludes them. Read only by `native_decide`. -/
def rankIdx6U : Nat → Nat
  | 93483 => 0
  | 93834 => 1
  | 93915 => 2
  | 93942 => 3
  | 99315 => 4
  | 99666 => 5
  | 99747 => 6
  | 99774 => 7
  | 129438 => 8
  | 132354 => 9
  | 133326 => 10
  | 135270 => 11
  | 138186 => 12
  | 139158 => 13
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6U (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 14 :=
  ⟨min (rankIdx6U (encT6U a b c d e f g h i j k)) 13, by omega⟩


/-- `1` of the `18` demanded maps and `2` of the `46638` forbidden ones, enough to separate the `14`
members from the other `139954` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6U` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6U : Fin 1 → Fin 18
  | 0 => 5
def x0idx6U : Fin 2 → Fin 46638
  | 0 => 9078
  | 1 => 9079

def endE06U (j : Fin 1) : Fin 6 → Fin 6 := endE6U (e0idx6U j)

def endX06U (j : Fin 2) : Fin 6 → Fin 6 := endX6U (x0idx6U j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6U (i : Fin 14) : Magma (Fin 6) := Magma.mk (mem6U i)

theorem end6U_isEndo (i : Fin 14) (j : Fin 18) : (end6U i).IsEndo (endE6U j) := by
  revert i j; native_decide

theorem end6U_not_isEndo (i : Fin 14) (j : Fin 46638) : ¬ (end6U i).IsEndo (endX6U j) := by
  revert i j; native_decide

/-- `rank6U` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6U` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6U (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6U a b c d e f g h i j k) endE06U endX06U = true) :
    mem6U (rank6U a b c d e f g h i j k) = tab6U a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `14` listed
members. -/
theorem mem_of_isExact6U (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6U a b c d e f g h i j k) endE06U endX06U = true) :
    ∃ idx, mem6U idx = tab6U a b c d e f g h i j k :=
  ⟨_, mem_rank6U a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6U`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6U` turns that into a member index. -/
theorem exists_end6U {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6U j))
    (hX : ∀ j, ¬ M.IsEndo (endX6U j)) : ∃ i, end6U i = M := by
  have hP : ∀ i, M.IsEndo (permE6U i) := by
    intro i; rw [permE6U_eq_endE6U]; exact hE (uidx6U i)
  have hop : M.op = Magma.transport permE6U tr6U (fun i ↦ M.op (rep6U i).1 (rep6U i).2) :=
    Magma.op_eq_transport (rep := rep6U) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U0) (a := (rep6U 0).1) (b := (rep6U 0).2)
    (val := val6U0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U1) (a := (rep6U 1).1) (b := (rep6U 1).2)
    (val := val6U1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U2) (a := (rep6U 2).1) (b := (rep6U 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U3) (a := (rep6U 3).1) (b := (rep6U 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U4) (a := (rep6U 4).1) (b := (rep6U 4).2)
    (val := val6U4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U5) (a := (rep6U 5).1) (b := (rep6U 5).2)
    (val := val6U5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U6) (a := (rep6U 6).1) (b := (rep6U 6).2)
    (val := val6U6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U7) (a := (rep6U 7).1) (b := (rep6U 7).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U8) (a := (rep6U 8).1) (b := (rep6U 8).2)
    (val := val6U8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U9) (a := (rep6U 9).1) (b := (rep6U 9).2)
    (val := val6U9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6U) (idx := stabIdx6U10) (a := (rep6U 10).1) (b := (rep6U 10).2)
    (val := val6U10) hP (by decide) (by decide)
  have hdec : dec6U a b c d e f g h i j k = fun i ↦ M.op (rep6U i).1 (rep6U i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
    · exact hi
    · exact hj
    · exact hk
  have key : tab6U a b c d e f g h i j k = M.op := by
    rw [tab6U_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6U a b c d e f g h i j k) endE06U endX06U = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6U j), fun j ↦ hX (x0idx6U j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6U a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`18` monoid of `Magma.endE6U`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6U {L L' : Law.NatMagmaLaw} {i : Fin 14}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6U i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6U j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6U i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6U
    (fun k ↦ (Magma.end6U_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6U_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
