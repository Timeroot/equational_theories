import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AF` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(2 3)(4 5), (0 2)(4 5)⟩`

`End(M)` is `30` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(2 3)(4 5)`, `(0 2)(4 5)`, `(0 2 3)`, `(0 3 2)`, `(0 3)(4
5)`. -/
def pE6AF0 : Fin 6 → Fin 6 := id
def pE6AF1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6AF2 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AF3 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5
def pE6AF4 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5
def pE6AF5 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4

def permE6AF : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6AF0
  | 1 => pE6AF1
  | 2 => pE6AF2
  | 3 => pE6AF3
  | 4 => pE6AF4
  | 5 => pE6AF5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `30` self-maps that must be endomorphisms: `000000`, `101100`, `202200`,
`303300`, `010011`, `111111`, `212211`, `313311`, `111141`, `111151`, `020022`, `121122`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AF : Fin 30 → Fin 46656
  | 0 => 0
  | 1 => 253
  | 2 => 506
  | 3 => 759
  | 4 => 9078
  | 5 => 9331
  | 6 => 9584
  | 7 => 9837
  | 8 => 13219
  | 9 => 14515
  | 10 => 18156
  | 11 => 18409
  | 12 => 18662
  | 13 => 18915
  | 14 => 27234
  | 15 => 27487
  | 16 => 27740
  | 17 => 27993
  | 18 => 32659
  | 19 => 36547
  | 20 => 37665
  | 21 => 37843
  | 22 => 38130
  | 23 => 38240
  | 24 => 40435
  | 25 => 44180
  | 26 => 44323
  | 27 => 44505
  | 28 => 44790
  | _ => 45619

def endE6AF (j : Fin 30) : Fin 6 → Fin 6 := allMaps6 (eidx6AF j)

/-- Indices of the other `46626`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AF : Array Nat := #[
  0, 253, 506, 759, 9078, 9331, 9584, 9837, 13219, 14515, 18156, 18409, 18662, 18915, 27234,
  27487, 27740, 27993, 32659, 36547, 37665, 37843, 38130, 38240, 40435, 44180, 44323, 44505,
  44790, 45619]

def xarr6AF : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AF.contains i)

def xidx6AF (j : Fin 46626) : Fin 46656 :=
  ⟨min (xarr6AF.getD j.1 0) 46655, by omega⟩

def endX6AF (j : Fin 46626) : Fin 6 → Fin 6 := allMaps6 (xidx6AF j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AF` is given. -/
def uidx6AF : Fin 6 → Fin 30
  | 0 => 28
  | 1 => 22
  | 2 => 23
  | 3 => 25
  | 4 => 27
  | 5 => 20

theorem permE6AF_eq_endE6AF (i : Fin 6) : permE6AF i = endE6AF (uidx6AF i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6AF : Fin 11 → Fin 6 × Fin 6
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
def tr6AF : Fin 6 → Fin 6 → Fin 11 × Fin 6
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
def stabIdx6AF0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AF0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AF1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AF1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AF2 : Fin 1 → Fin 6
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AF3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AF4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AF4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `1`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx6AF5 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def val6AF5 : Fin 1 → Fin 6
  | 0 => 1

/-- The `3` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AF6 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6AF6 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AF7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `3` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AF8 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6AF8 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AF9 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6AF9 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `3` group elements fixing both coordinates of orbit `10`'s representative, and hence its
value: that value must be one of `1`, `4`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdx6AF10 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
def val6AF10 : Fin 3 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 5

/-- The `11` orbit values named by the family's arguments. -/
def dec6AF (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 11 → Fin 6
  | 0 => val6AF0 a
  | 1 => val6AF1 b
  | 2 => c
  | 3 => d
  | 4 => val6AF4 e
  | 5 => val6AF5 f
  | 6 => val6AF6 g
  | 7 => h
  | 8 => val6AF8 i
  | 9 => val6AF9 j
  | 10 => val6AF10 k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AF_eq_transport`). -/
def tab6AF (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AF0 a
  | 0, 1 => val6AF1 b
  | 0, 2 => c
  | 0, 3 => pE6AF1 c
  | 0, 4 => d
  | 0, 5 => pE6AF1 d
  | 1, 0 => val6AF4 e
  | 1, 1 => val6AF5 f
  | 1, 2 => pE6AF2 (val6AF4 e)
  | 1, 3 => pE6AF4 (val6AF4 e)
  | 1, 4 => val6AF6 g
  | 1, 5 => pE6AF1 (val6AF6 g)
  | 2, 0 => pE6AF2 c
  | 2, 1 => pE6AF2 (val6AF1 b)
  | 2, 2 => pE6AF2 (val6AF0 a)
  | 2, 3 => pE6AF3 c
  | 2, 4 => pE6AF3 d
  | 2, 5 => pE6AF2 d
  | 3, 0 => pE6AF4 c
  | 3, 1 => pE6AF4 (val6AF1 b)
  | 3, 2 => pE6AF5 c
  | 3, 3 => pE6AF4 (val6AF0 a)
  | 3, 4 => pE6AF4 d
  | 3, 5 => pE6AF5 d
  | 4, 0 => h
  | 4, 1 => val6AF8 i
  | 4, 2 => pE6AF3 h
  | 4, 3 => pE6AF4 h
  | 4, 4 => val6AF9 j
  | 4, 5 => val6AF10 k
  | 5, 0 => pE6AF1 h
  | 5, 1 => pE6AF1 (val6AF8 i)
  | 5, 2 => pE6AF2 h
  | 5, 3 => pE6AF5 h
  | 5, 4 => pE6AF1 (val6AF10 k)
  | 5, 5 => pE6AF1 (val6AF9 j)

theorem tab6AF_eq_transport (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3)
    (h : Fin 6) (i j k : Fin 3) :
    tab6AF a b c d e f g h i j k = Magma.transport permE6AF tr6AF (dec6AF a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `139968` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AF : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AF 0 0 0 2 1 0 0 1 0 0 0
  | 1 => tab6AF 0 0 0 3 1 0 0 1 0 0 0
  | 2 => tab6AF 0 1 2 1 0 0 0 2 0 0 0
  | 3 => tab6AF 0 1 2 1 0 0 0 3 0 0 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6AF` is addressed. -/
def encT6AF (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
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

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExact6AF` can name one
rather than search the list for it. The `139964` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6AF` excludes them. Read only by `native_decide`. -/
def rankIdx6AF : Nat → Nat
  | 2457 => 0
  | 3429 => 1
  | 47682 => 2
  | 47709 => 3
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AF (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3) : Fin 4 :=
  ⟨min (rankIdx6AF (encT6AF a b c d e f g h i j k)) 3, by omega⟩


/-- `3` of the `30` demanded maps and `2` of the `46626` forbidden ones, enough to separate the `4`
members from the other `139964` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AF` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AF : Fin 3 → Fin 30
  | 0 => 2
  | 1 => 8
  | 2 => 19
def x0idx6AF : Fin 2 → Fin 46626
  | 0 => 0
  | 1 => 5

def endE06AF (j : Fin 3) : Fin 6 → Fin 6 := endE6AF (e0idx6AF j)

def endX06AF (j : Fin 2) : Fin 6 → Fin 6 := endX6AF (x0idx6AF j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AF (i : Fin 4) : Magma (Fin 6) := Magma.mk (mem6AF i)

theorem end6AF_isEndo (i : Fin 4) (j : Fin 30) : (end6AF i).IsEndo (endE6AF j) := by
  revert i j; native_decide

theorem end6AF_not_isEndo (i : Fin 4) (j : Fin 46626) : ¬ (end6AF i).IsEndo (endX6AF j) := by
  revert i j; native_decide

/-- `rank6AF` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AF` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AF (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3) (h : Fin 6)
    (i j k : Fin 3)
    (hx : Magma.isExact (tab6AF a b c d e f g h i j k) endE06AF endX06AF = true) :
    mem6AF (rank6AF a b c d e f g h i j k) = tab6AF a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `4` listed
members. -/
theorem mem_of_isExact6AF (a b : Fin 2) (c d : Fin 6) (e : Fin 2) (f : Fin 1) (g : Fin 3)
    (h : Fin 6) (i j k : Fin 3)
    (hx : Magma.isExact (tab6AF a b c d e f g h i j k) endE06AF endX06AF = true) :
    ∃ idx, mem6AF idx = tab6AF a b c d e f g h i j k :=
  ⟨_, mem_rank6AF a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AF`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AF` turns that into a member index. -/
theorem exists_end6AF {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AF j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AF j)) : ∃ i, end6AF i = M := by
  have hP : ∀ i, M.IsEndo (permE6AF i) := by
    intro i; rw [permE6AF_eq_endE6AF]; exact hE (uidx6AF i)
  have hop : M.op = Magma.transport permE6AF tr6AF (fun i ↦ M.op (rep6AF i).1 (rep6AF i).2) :=
    Magma.op_eq_transport (rep := rep6AF) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF0) (a := (rep6AF 0).1) (b := (rep6AF 0).2)
    (val := val6AF0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF1) (a := (rep6AF 1).1) (b := (rep6AF 1).2)
    (val := val6AF1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF2) (a := (rep6AF 2).1) (b := (rep6AF 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF3) (a := (rep6AF 3).1) (b := (rep6AF 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF4) (a := (rep6AF 4).1) (b := (rep6AF 4).2)
    (val := val6AF4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF5) (a := (rep6AF 5).1) (b := (rep6AF 5).2)
    (val := val6AF5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF6) (a := (rep6AF 6).1) (b := (rep6AF 6).2)
    (val := val6AF6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF7) (a := (rep6AF 7).1) (b := (rep6AF 7).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF8) (a := (rep6AF 8).1) (b := (rep6AF 8).2)
    (val := val6AF8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF9) (a := (rep6AF 9).1) (b := (rep6AF 9).2)
    (val := val6AF9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6AF) (idx := stabIdx6AF10) (a := (rep6AF 10).1) (b := (rep6AF 10).2)
    (val := val6AF10) hP (by decide) (by decide)
  have hdec : dec6AF a b c d e f g h i j k = fun i ↦ M.op (rep6AF i).1 (rep6AF i).2 := by
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
  have key : tab6AF a b c d e f g h i j k = M.op := by
    rw [tab6AF_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AF a b c d e f g h i j k) endE06AF endX06AF = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AF j), fun j ↦ hX (x0idx6AF j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AF a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`30` monoid of `Magma.endE6AF`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AF {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AF i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AF j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AF i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AF
    (fun k ↦ (Magma.end6AF_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AF_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
