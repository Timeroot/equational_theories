import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `L` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(2 3)(4 5), (2 4)(3 5), (2 4 3 5)⟩`

`End(M)` is `35` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `11` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(2 3)`, `(2 3)(4 5)`, `(2 4)(3 5)`, `(2 4 3 5)`,
`(2 5 3 4)`, `(2 5)(3 4)`. -/
def pE6L0 : Fin 6 → Fin 6 := id
def pE6L1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6L2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5
def pE6L3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6L4 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3
def pE6L5 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
def pE6L6 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3
def pE6L7 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2

def permE6L : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6L0
  | 1 => pE6L1
  | 2 => pE6L2
  | 3 => pE6L3
  | 4 => pE6L4
  | 5 => pE6L5
  | 6 => pE6L6
  | 7 => pE6L7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `35` self-maps that must be endomorphisms: `111100`, `112200`, `113300`,
`114400`, `115500`, `110011`, `111111`, `112211`, `113311`, `114411`, `115511`, `110022`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6L : Fin 35 → Fin 46656
  | 0 => 259
  | 1 => 511
  | 2 => 763
  | 3 => 1015
  | 4 => 1267
  | 5 => 9079
  | 6 => 9331
  | 7 => 9583
  | 8 => 9835
  | 9 => 10087
  | 10 => 10339
  | 11 => 18151
  | 12 => 18403
  | 13 => 19159
  | 14 => 19411
  | 15 => 20490
  | 16 => 20670
  | 17 => 26970
  | 18 => 27150
  | 19 => 27223
  | 20 => 27475
  | 21 => 28231
  | 22 => 28483
  | 23 => 36295
  | 24 => 36547
  | 25 => 36799
  | 26 => 37051
  | 27 => 38130
  | 28 => 38310
  | 29 => 44610
  | 30 => 44790
  | 31 => 45367
  | 32 => 45619
  | 33 => 45871
  | _ => 46123

def endE6L (j : Fin 35) : Fin 6 → Fin 6 := allMaps6 (eidx6L j)

/-- Indices of the other `46621`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6L : Array Nat := #[
  259, 511, 763, 1015, 1267, 9079, 9331, 9583, 9835, 10087, 10339, 18151, 18403, 19159, 19411,
  20490, 20670, 26970, 27150, 27223, 27475, 28231, 28483, 36295, 36547, 36799, 37051, 38130,
  38310, 44610, 44790, 45367, 45619, 45871, 46123]

def xarr6L : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6L.contains i)

def xidx6L (j : Fin 46621) : Fin 46656 :=
  ⟨min (xarr6L.getD j.1 0) 46655, by omega⟩

def endX6L (j : Fin 46621) : Fin 6 → Fin 6 := allMaps6 (xidx6L j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6L` is given. -/
def uidx6L : Fin 8 → Fin 35
  | 0 => 30
  | 1 => 28
  | 2 => 29
  | 3 => 27
  | 4 => 18
  | 5 => 16
  | 6 => 17
  | 7 => 15

theorem permE6L_eq_endE6L (i : Fin 8) : permE6L i = endE6L (uidx6L i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `11`, so an invariant
operation is `11` values. -/
def rep6L : Fin 11 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)
  | 6 => (2, 0)
  | 7 => (2, 1)
  | 8 => (2, 2)
  | 9 => (2, 3)
  | 10 => (2, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6L : Fin 6 → Fin 6 → Fin 11 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 2)
  | 0, 4 => (2, 4)
  | 0, 5 => (2, 6)
  | 1, 0 => (3, 0)
  | 1, 1 => (4, 0)
  | 1, 2 => (5, 0)
  | 1, 3 => (5, 2)
  | 1, 4 => (5, 4)
  | 1, 5 => (5, 6)
  | 2, 0 => (6, 0)
  | 2, 1 => (7, 0)
  | 2, 2 => (8, 0)
  | 2, 3 => (9, 0)
  | 2, 4 => (10, 0)
  | 2, 5 => (10, 1)
  | 3, 0 => (6, 2)
  | 3, 1 => (7, 2)
  | 3, 2 => (9, 2)
  | 3, 3 => (8, 2)
  | 3, 4 => (10, 2)
  | 3, 5 => (10, 3)
  | 4, 0 => (6, 4)
  | 4, 1 => (7, 4)
  | 4, 2 => (10, 4)
  | 4, 3 => (10, 5)
  | 4, 4 => (8, 4)
  | 4, 5 => (9, 4)
  | 5, 0 => (6, 6)
  | 5, 1 => (7, 6)
  | 5, 2 => (10, 6)
  | 5, 3 => (10, 7)
  | 5, 4 => (9, 6)
  | 5, 5 => (8, 6)

/-- The `8` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6L0 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6L0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6L1 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6L1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6L2 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6L2 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `8` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6L3 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6L3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `8` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6L4 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
def val6L4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6L5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6L5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6L6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6L6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6L7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6L7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `8`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6L8 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6L8 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `9`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6L9 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6L9 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `10`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6L10 : Fin 1 → Fin 8
  | 0 => 0

/-- The `11` orbit values named by the family's arguments. -/
def dec6L (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 11 → Fin 6
  | 0 => val6L0 a
  | 1 => val6L1 b
  | 2 => val6L2 c
  | 3 => val6L3 d
  | 4 => val6L4 e
  | 5 => val6L5 f
  | 6 => val6L6 g
  | 7 => val6L7 h
  | 8 => val6L8 i
  | 9 => val6L9 j
  | 10 => k

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6L_eq_transport`). -/
def tab6L (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6L0 a
  | 0, 1 => val6L1 b
  | 0, 2 => val6L2 c
  | 0, 3 => pE6L2 (val6L2 c)
  | 0, 4 => pE6L4 (val6L2 c)
  | 0, 5 => pE6L6 (val6L2 c)
  | 1, 0 => val6L3 d
  | 1, 1 => val6L4 e
  | 1, 2 => val6L5 f
  | 1, 3 => pE6L2 (val6L5 f)
  | 1, 4 => pE6L4 (val6L5 f)
  | 1, 5 => pE6L6 (val6L5 f)
  | 2, 0 => val6L6 g
  | 2, 1 => val6L7 h
  | 2, 2 => val6L8 i
  | 2, 3 => val6L9 j
  | 2, 4 => k
  | 2, 5 => pE6L1 k
  | 3, 0 => pE6L2 (val6L6 g)
  | 3, 1 => pE6L2 (val6L7 h)
  | 3, 2 => pE6L2 (val6L9 j)
  | 3, 3 => pE6L2 (val6L8 i)
  | 3, 4 => pE6L2 k
  | 3, 5 => pE6L3 k
  | 4, 0 => pE6L4 (val6L6 g)
  | 4, 1 => pE6L4 (val6L7 h)
  | 4, 2 => pE6L4 k
  | 4, 3 => pE6L5 k
  | 4, 4 => pE6L4 (val6L8 i)
  | 4, 5 => pE6L4 (val6L9 j)
  | 5, 0 => pE6L6 (val6L6 g)
  | 5, 1 => pE6L6 (val6L7 h)
  | 5, 2 => pE6L6 k
  | 5, 3 => pE6L7 k
  | 5, 4 => pE6L6 (val6L9 j)
  | 5, 5 => pE6L6 (val6L8 i)

theorem tab6L_eq_transport (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) :
    tab6L a b c d e f g h i j k = Magma.transport permE6L tr6L (dec6L a b c d e f g h i j k) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `393216` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6L : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6L 1 0 0 1 1 1 2 2 1 0 2
  | 1 => tab6L 1 1 2 0 1 2 0 1 1 0 4

/-- The arguments as one mixed-radix index, which is how `rankIdx6L` is addressed. -/
def encT6L (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Nat :=
  a.1 * 196608 +
    b.1 * 98304 +
    c.1 * 24576 +
    d.1 * 12288 +
    e.1 * 6144 +
    f.1 * 1536 +
    g.1 * 384 +
    h.1 * 96 +
    i.1 * 24 +
    j.1 * 6 +
    k.1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6L` can name one
rather than search the list for it. The `393214` tuples that are not members fall through to `0`;
the hypothesis of `mem_rank6L` excludes them. Read only by `native_decide`. -/
def rankIdx6L : Nat → Nat
  | 217562 => 0
  | 353404 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6L (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6) : Fin 2 :=
  ⟨min (rankIdx6L (encT6L a b c d e f g h i j k)) 1, by omega⟩


/-- `2` of the `35` demanded maps and `2` of the `46621` forbidden ones, enough to separate the `2`
members from the other `393214` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6L` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6L : Fin 2 → Fin 35
  | 0 => 1
  | 1 => 13
def x0idx6L : Fin 2 → Fin 46621
  | 0 => 7
  | 1 => 259

def endE06L (j : Fin 2) : Fin 6 → Fin 6 := endE6L (e0idx6L j)

def endX06L (j : Fin 2) : Fin 6 → Fin 6 := endX6L (x0idx6L j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6L (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6L i)

theorem end6L_isEndo (i : Fin 2) (j : Fin 35) : (end6L i).IsEndo (endE6L j) := by
  revert i j; native_decide

theorem end6L_not_isEndo (i : Fin 2) (j : Fin 46621) : ¬ (end6L i).IsEndo (endX6L j) := by
  revert i j; native_decide

/-- `rank6L` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6L` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6L (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6L a b c d e f g h i j k) endE06L endX06L = true) :
    mem6L (rank6L a b c d e f g h i j k) = tab6L a b c d e f g h i j k := by
  revert hx; revert a b c d e f g h i j k; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6L (a b : Fin 2) (c : Fin 4) (d e : Fin 2) (f g h i j : Fin 4) (k : Fin 6)
    (hx : Magma.isExact (tab6L a b c d e f g h i j k) endE06L endX06L = true) :
    ∃ idx, mem6L idx = tab6L a b c d e f g h i j k :=
  ⟨_, mem_rank6L a b c d e f g h i j k hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6L`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6L` turns that into a member index. -/
theorem exists_end6L {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6L j))
    (hX : ∀ j, ¬ M.IsEndo (endX6L j)) : ∃ i, end6L i = M := by
  have hP : ∀ i, M.IsEndo (permE6L i) := by
    intro i; rw [permE6L_eq_endE6L]; exact hE (uidx6L i)
  have hop : M.op = Magma.transport permE6L tr6L (fun i ↦ M.op (rep6L i).1 (rep6L i).2) :=
    Magma.op_eq_transport (rep := rep6L) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L0) (a := (rep6L 0).1) (b := (rep6L 0).2)
    (val := val6L0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L1) (a := (rep6L 1).1) (b := (rep6L 1).2)
    (val := val6L1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L2) (a := (rep6L 2).1) (b := (rep6L 2).2)
    (val := val6L2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L3) (a := (rep6L 3).1) (b := (rep6L 3).2)
    (val := val6L3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L4) (a := (rep6L 4).1) (b := (rep6L 4).2)
    (val := val6L4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L5) (a := (rep6L 5).1) (b := (rep6L 5).2)
    (val := val6L5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L6) (a := (rep6L 6).1) (b := (rep6L 6).2)
    (val := val6L6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L7) (a := (rep6L 7).1) (b := (rep6L 7).2)
    (val := val6L7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L8) (a := (rep6L 8).1) (b := (rep6L 8).2)
    (val := val6L8) hP (by decide) (by decide)
  obtain ⟨j, hj⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L9) (a := (rep6L 9).1) (b := (rep6L 9).2)
    (val := val6L9) hP (by decide) (by decide)
  obtain ⟨k, hk⟩ := Magma.exists_val_of_isEndo
    (E := permE6L) (idx := stabIdx6L10) (a := (rep6L 10).1) (b := (rep6L 10).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6L a b c d e f g h i j k = fun i ↦ M.op (rep6L i).1 (rep6L i).2 := by
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
  have key : tab6L a b c d e f g h i j k = M.op := by
    rw [tab6L_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6L a b c d e f g h i j k) endE06L endX06L = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6L j), fun j ↦ hX (x0idx6L j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6L a b c d e f g h i j k hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`35` monoid of `Magma.endE6L`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6L {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6L i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6L j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6L i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6L
    (fun k ↦ (Magma.end6L_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6L_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
