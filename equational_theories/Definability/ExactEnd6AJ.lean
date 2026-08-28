import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AJ` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(0 1 2)(3 4 5), (1 2)(4 5)⟩`

`End(M)` is `48` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `8` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(1 2)(4 5)`, `(0 1)(3 4)`, `(0 1 2)(3 4 5)`, `(0 2 1)(3 5
4)`, `(0 2)(3 5)`. -/
def pE6AJ0 : Fin 6 → Fin 6 := id
def pE6AJ1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AJ2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6AJ3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pE6AJ4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pE6AJ5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3

def permE6AJ : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6AJ0
  | 1 => pE6AJ1
  | 2 => pE6AJ2
  | 3 => pE6AJ3
  | 4 => pE6AJ4
  | 5 => pE6AJ5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `48` self-maps that must be endomorphisms: `000000`, `000300`, `000030`,
`000330`, `111111`, `111411`, `111141`, `111441`, `222222`, `222522`, `222252`, `222552`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AJ : Fin 48 → Fin 46656
  | 0 => 0
  | 1 => 648
  | 2 => 3888
  | 3 => 4536
  | 4 => 9331
  | 5 => 9979
  | 6 => 13219
  | 7 => 13867
  | 8 => 18662
  | 9 => 19310
  | 10 => 22550
  | 11 => 23198
  | 12 => 23328
  | 13 => 23976
  | 14 => 27216
  | 15 => 27864
  | 16 => 28081
  | 17 => 28298
  | 18 => 29166
  | 19 => 29383
  | 20 => 29600
  | 21 => 30468
  | 22 => 30685
  | 23 => 30902
  | 24 => 32659
  | 25 => 33307
  | 26 => 35676
  | 27 => 35893
  | 28 => 36110
  | 29 => 36547
  | 30 => 36978
  | 31 => 37195
  | 32 => 37412
  | 33 => 38280
  | 34 => 38497
  | 35 => 38714
  | 36 => 41990
  | 37 => 42638
  | 38 => 43488
  | 39 => 43705
  | 40 => 43922
  | 41 => 44790
  | 42 => 45007
  | 43 => 45224
  | 44 => 45878
  | 45 => 46092
  | 46 => 46309
  | _ => 46526

def endE6AJ (j : Fin 48) : Fin 6 → Fin 6 := allMaps6 (eidx6AJ j)

/-- Indices of the other `46608`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AJ : Array Nat := #[
  0, 648, 3888, 4536, 9331, 9979, 13219, 13867, 18662, 19310, 22550, 23198, 23328, 23976, 27216,
  27864, 28081, 28298, 29166, 29383, 29600, 30468, 30685, 30902, 32659, 33307, 35676, 35893,
  36110, 36547, 36978, 37195, 37412, 38280, 38497, 38714, 41990, 42638, 43488, 43705, 43922,
  44790, 45007, 45224, 45878, 46092, 46309, 46526]

def xarr6AJ : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AJ.contains i)

def xidx6AJ (j : Fin 46608) : Fin 46656 :=
  ⟨min (xarr6AJ.getD j.1 0) 46655, by omega⟩

def endX6AJ (j : Fin 46608) : Fin 6 → Fin 6 := allMaps6 (xidx6AJ j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AJ` is given. -/
def uidx6AJ : Fin 6 → Fin 48
  | 0 => 41
  | 1 => 33
  | 2 => 39
  | 3 => 22
  | 4 => 28
  | 5 => 20

theorem permE6AJ_eq_endE6AJ (i : Fin 6) : permE6AJ i = endE6AJ (uidx6AJ i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `8`, so an invariant
operation is `8` values. -/
def rep6AJ : Fin 8 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (3, 0)
  | 5 => (3, 1)
  | 6 => (3, 3)
  | 7 => (3, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6AJ : Fin 6 → Fin 6 → Fin 8 × Fin 6
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 3)
  | 1, 3 => (3, 2)
  | 1, 4 => (2, 2)
  | 1, 5 => (3, 3)
  | 2, 0 => (1, 4)
  | 2, 1 => (1, 5)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 4)
  | 2, 4 => (3, 5)
  | 2, 5 => (2, 4)
  | 3, 0 => (4, 0)
  | 3, 1 => (5, 0)
  | 3, 2 => (5, 1)
  | 3, 3 => (6, 0)
  | 3, 4 => (7, 0)
  | 3, 5 => (7, 1)
  | 4, 0 => (5, 2)
  | 4, 1 => (4, 2)
  | 4, 2 => (5, 3)
  | 4, 3 => (7, 2)
  | 4, 4 => (6, 2)
  | 4, 5 => (7, 3)
  | 5, 0 => (5, 4)
  | 5, 1 => (5, 5)
  | 5, 2 => (4, 4)
  | 5, 3 => (7, 4)
  | 5, 4 => (7, 5)
  | 5, 5 => (6, 4)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AJ0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AJ0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AJ1 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AJ2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AJ2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AJ3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AJ4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AJ4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AJ5 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AJ6 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6AJ6 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AJ7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `8` orbit values named by the family's arguments. -/
def dec6AJ (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 8 → Fin 6
  | 0 => val6AJ0 a
  | 1 => b
  | 2 => val6AJ2 c
  | 3 => d
  | 4 => val6AJ4 e
  | 5 => f
  | 6 => val6AJ6 g
  | 7 => h

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AJ_eq_transport`). -/
def tab6AJ (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AJ0 a
  | 0, 1 => b
  | 0, 2 => pE6AJ1 b
  | 0, 3 => val6AJ2 c
  | 0, 4 => d
  | 0, 5 => pE6AJ1 d
  | 1, 0 => pE6AJ2 b
  | 1, 1 => pE6AJ2 (val6AJ0 a)
  | 1, 2 => pE6AJ3 b
  | 1, 3 => pE6AJ2 d
  | 1, 4 => pE6AJ2 (val6AJ2 c)
  | 1, 5 => pE6AJ3 d
  | 2, 0 => pE6AJ4 b
  | 2, 1 => pE6AJ5 b
  | 2, 2 => pE6AJ4 (val6AJ0 a)
  | 2, 3 => pE6AJ4 d
  | 2, 4 => pE6AJ5 d
  | 2, 5 => pE6AJ4 (val6AJ2 c)
  | 3, 0 => val6AJ4 e
  | 3, 1 => f
  | 3, 2 => pE6AJ1 f
  | 3, 3 => val6AJ6 g
  | 3, 4 => h
  | 3, 5 => pE6AJ1 h
  | 4, 0 => pE6AJ2 f
  | 4, 1 => pE6AJ2 (val6AJ4 e)
  | 4, 2 => pE6AJ3 f
  | 4, 3 => pE6AJ2 h
  | 4, 4 => pE6AJ2 (val6AJ6 g)
  | 4, 5 => pE6AJ3 h
  | 5, 0 => pE6AJ4 f
  | 5, 1 => pE6AJ5 f
  | 5, 2 => pE6AJ4 (val6AJ4 e)
  | 5, 3 => pE6AJ4 h
  | 5, 4 => pE6AJ5 h
  | 5, 5 => pE6AJ4 (val6AJ6 g)

theorem tab6AJ_eq_transport (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6) :
    tab6AJ a b c d e f g h = Magma.transport permE6AJ tr6AJ (dec6AJ a b c d e f g h) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `14` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `20736` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6AJ : Fin 14 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AJ 0 0 0 0 0 0 0 1
  | 1 => tab6AJ 0 0 0 0 0 1 0 0
  | 2 => tab6AJ 0 0 0 0 0 1 0 1
  | 3 => tab6AJ 0 0 0 1 0 0 0 0
  | 4 => tab6AJ 0 0 0 1 0 0 0 1
  | 5 => tab6AJ 0 0 0 1 0 1 0 0
  | 6 => tab6AJ 0 0 0 1 0 1 0 1
  | 7 => tab6AJ 0 1 0 0 0 0 0 0
  | 8 => tab6AJ 0 1 0 0 0 0 0 1
  | 9 => tab6AJ 0 1 0 0 0 1 0 0
  | 10 => tab6AJ 0 1 0 0 0 1 0 1
  | 11 => tab6AJ 0 1 0 1 0 0 0 0
  | 12 => tab6AJ 0 1 0 1 0 0 0 1
  | 13 => tab6AJ 0 1 0 1 0 1 0 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6AJ` is addressed. -/
def encT6AJ (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Nat :=
  a.1 * 10368 +
    b.1 * 1728 +
    c.1 * 864 +
    d.1 * 144 +
    e.1 * 72 +
    f.1 * 12 +
    g.1 * 6 +
    h.1

/-- Which of the `14` members a given invariant tuple is, so that `mem_of_isExact6AJ` can name one
rather than search the list for it. The `20722` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6AJ` excludes them. Read only by `native_decide`. -/
def rankIdx6AJ : Nat → Nat
  | 1 => 0
  | 12 => 1
  | 13 => 2
  | 144 => 3
  | 145 => 4
  | 156 => 5
  | 157 => 6
  | 1728 => 7
  | 1729 => 8
  | 1740 => 9
  | 1741 => 10
  | 1872 => 11
  | 1873 => 12
  | 1884 => 13
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AJ (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 14 :=
  ⟨min (rankIdx6AJ (encT6AJ a b c d e f g h)) 13, by omega⟩


/-- `2` of the `48` demanded maps and `2` of the `46608` forbidden ones, enough to separate the `14`
members from the other `20722` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AJ` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AJ : Fin 2 → Fin 48
  | 0 => 3
  | 1 => 16
def x0idx6AJ : Fin 2 → Fin 46608
  | 0 => 128
  | 1 => 216

def endE06AJ (j : Fin 2) : Fin 6 → Fin 6 := endE6AJ (e0idx6AJ j)

def endX06AJ (j : Fin 2) : Fin 6 → Fin 6 := endX6AJ (x0idx6AJ j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AJ (i : Fin 14) : Magma (Fin 6) := Magma.mk (mem6AJ i)

theorem end6AJ_isEndo (i : Fin 14) (j : Fin 48) : (end6AJ i).IsEndo (endE6AJ j) := by
  revert i j; native_decide

theorem end6AJ_not_isEndo (i : Fin 14) (j : Fin 46608) : ¬ (end6AJ i).IsEndo (endX6AJ j) := by
  revert i j; native_decide

/-- `rank6AJ` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AJ` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AJ (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6)
    (hx : Magma.isExact (tab6AJ a b c d e f g h) endE06AJ endX06AJ = true) :
    mem6AJ (rank6AJ a b c d e f g h) = tab6AJ a b c d e f g h := by
  revert hx; revert a b c d e f g h; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `14` listed
members. -/
theorem mem_of_isExact6AJ (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6)
    (hx : Magma.isExact (tab6AJ a b c d e f g h) endE06AJ endX06AJ = true) :
    ∃ idx, mem6AJ idx = tab6AJ a b c d e f g h :=
  ⟨_, mem_rank6AJ a b c d e f g h hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AJ`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AJ` turns that into a member index. -/
theorem exists_end6AJ {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AJ j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AJ j)) : ∃ i, end6AJ i = M := by
  have hP : ∀ i, M.IsEndo (permE6AJ i) := by
    intro i; rw [permE6AJ_eq_endE6AJ]; exact hE (uidx6AJ i)
  have hop : M.op = Magma.transport permE6AJ tr6AJ (fun i ↦ M.op (rep6AJ i).1 (rep6AJ i).2) :=
    Magma.op_eq_transport (rep := rep6AJ) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ0) (a := (rep6AJ 0).1) (b := (rep6AJ 0).2)
    (val := val6AJ0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ1) (a := (rep6AJ 1).1) (b := (rep6AJ 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ2) (a := (rep6AJ 2).1) (b := (rep6AJ 2).2)
    (val := val6AJ2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ3) (a := (rep6AJ 3).1) (b := (rep6AJ 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ4) (a := (rep6AJ 4).1) (b := (rep6AJ 4).2)
    (val := val6AJ4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ5) (a := (rep6AJ 5).1) (b := (rep6AJ 5).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ6) (a := (rep6AJ 6).1) (b := (rep6AJ 6).2)
    (val := val6AJ6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AJ) (idx := stabIdx6AJ7) (a := (rep6AJ 7).1) (b := (rep6AJ 7).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6AJ a b c d e f g h = fun i ↦ M.op (rep6AJ i).1 (rep6AJ i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
  have key : tab6AJ a b c d e f g h = M.op := by
    rw [tab6AJ_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AJ a b c d e f g h) endE06AJ endX06AJ = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AJ j), fun j ↦ hX (x0idx6AJ j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AJ a b c d e f g h hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`48` monoid of `Magma.endE6AJ`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AJ {L L' : Law.NatMagmaLaw} {i : Fin 14}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AJ i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AJ j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AJ i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AJ
    (fun k ↦ (Magma.end6AJ_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AJ_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
