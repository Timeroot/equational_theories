import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `Y` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 2)(1 4)(3 5), (0 2)(1 4 3 5)⟩`

`End(M)` is `26` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `9` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(1 3)`, `(1 3)(4 5)`, `(0 2)(1 4)(3 5)`, `(0 2)(1
4 3 5)`, `(0 2)(1 5 3 4)`, `(0 2)(1 5)(3 4)`. -/
def pE6Y0 : Fin 6 → Fin 6 := id
def pE6Y1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6Y2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5
def pE6Y3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4
def pE6Y4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 3
def pE6Y5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 1
def pE6Y6 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 3
def pE6Y7 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1

def permE6Y : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6Y0
  | 1 => pE6Y1
  | 2 => pE6Y2
  | 3 => pE6Y3
  | 4 => pE6Y4
  | 5 => pE6Y5
  | 6 => pE6Y6
  | 7 => pE6Y7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `26` self-maps that must be endomorphisms: `000000`, `030100`, `010300`,
`000031`, `030131`, `010331`, `250431`, `240531`, `222222`, `252422`, `242522`, `000013`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6Y : Fin 26 → Fin 46656
  | 0 => 0
  | 1 => 234
  | 2 => 654
  | 3 => 11664
  | 4 => 11898
  | 5 => 12318
  | 6 => 12560
  | 7 => 12770
  | 8 => 18662
  | 9 => 19112
  | 10 => 19322
  | 11 => 24624
  | 12 => 24858
  | 13 => 25278
  | 14 => 25520
  | 15 => 25730
  | 16 => 37890
  | 17 => 38102
  | 18 => 38310
  | 19 => 38552
  | 20 => 38762
  | 21 => 44370
  | 22 => 44582
  | 23 => 44790
  | 24 => 45032
  | _ => 45242

def endE6Y (j : Fin 26) : Fin 6 → Fin 6 := allMaps6 (eidx6Y j)

/-- Indices of the other `46630`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6Y : Array Nat := #[
  0, 234, 654, 11664, 11898, 12318, 12560, 12770, 18662, 19112, 19322, 24624, 24858, 25278,
  25520, 25730, 37890, 38102, 38310, 38552, 38762, 44370, 44582, 44790, 45032, 45242]

def xarr6Y : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6Y.contains i)

def xidx6Y (j : Fin 46630) : Fin 46656 :=
  ⟨min (xarr6Y.getD j.1 0) 46655, by omega⟩

def endX6Y (j : Fin 46630) : Fin 6 → Fin 6 := allMaps6 (xidx6Y j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6Y` is given. -/
def uidx6Y : Fin 8 → Fin 26
  | 0 => 23
  | 1 => 18
  | 2 => 21
  | 3 => 16
  | 4 => 15
  | 5 => 7
  | 6 => 14
  | 7 => 6

theorem permE6Y_eq_endE6Y (i : Fin 8) : permE6Y i = endE6Y (uidx6Y i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `9`, so an invariant
operation is `9` values. -/
def rep6Y : Fin 9 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)
  | 4 => (1, 0)
  | 5 => (1, 1)
  | 6 => (1, 2)
  | 7 => (1, 3)
  | 8 => (1, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6Y : Fin 6 → Fin 6 → Fin 9 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (1, 2)
  | 0, 4 => (3, 0)
  | 0, 5 => (3, 1)
  | 1, 0 => (4, 0)
  | 1, 1 => (5, 0)
  | 1, 2 => (6, 0)
  | 1, 3 => (7, 0)
  | 1, 4 => (8, 0)
  | 1, 5 => (8, 1)
  | 2, 0 => (2, 4)
  | 2, 1 => (3, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 5)
  | 2, 4 => (1, 4)
  | 2, 5 => (1, 6)
  | 3, 0 => (4, 2)
  | 3, 1 => (7, 2)
  | 3, 2 => (6, 2)
  | 3, 3 => (5, 2)
  | 3, 4 => (8, 2)
  | 3, 5 => (8, 3)
  | 4, 0 => (6, 4)
  | 4, 1 => (8, 4)
  | 4, 2 => (4, 4)
  | 4, 3 => (8, 5)
  | 4, 4 => (5, 4)
  | 4, 5 => (7, 4)
  | 5, 0 => (6, 6)
  | 5, 1 => (8, 6)
  | 5, 2 => (4, 6)
  | 5, 3 => (8, 7)
  | 5, 4 => (7, 6)
  | 5, 5 => (5, 6)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Y0 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6Y0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Y1 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Y1 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6Y2 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6Y2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `2`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Y3 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 2
def val6Y3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Y4 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Y4 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Y5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Y5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Y6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Y6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6Y7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6Y7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `8`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6Y8 : Fin 1 → Fin 8
  | 0 => 0

/-- The `9` orbit values named by the family's arguments. -/
def dec6Y (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 9 → Fin 6
  | 0 => val6Y0 a
  | 1 => val6Y1 b
  | 2 => val6Y2 c
  | 3 => val6Y3 d
  | 4 => val6Y4 e
  | 5 => val6Y5 f
  | 6 => val6Y6 g
  | 7 => val6Y7 h
  | 8 => i

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6Y_eq_transport`). -/
def tab6Y (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6Y0 a
  | 0, 1 => val6Y1 b
  | 0, 2 => val6Y2 c
  | 0, 3 => pE6Y2 (val6Y1 b)
  | 0, 4 => val6Y3 d
  | 0, 5 => pE6Y1 (val6Y3 d)
  | 1, 0 => val6Y4 e
  | 1, 1 => val6Y5 f
  | 1, 2 => val6Y6 g
  | 1, 3 => val6Y7 h
  | 1, 4 => i
  | 1, 5 => pE6Y1 i
  | 2, 0 => pE6Y4 (val6Y2 c)
  | 2, 1 => pE6Y4 (val6Y3 d)
  | 2, 2 => pE6Y4 (val6Y0 a)
  | 2, 3 => pE6Y5 (val6Y3 d)
  | 2, 4 => pE6Y4 (val6Y1 b)
  | 2, 5 => pE6Y6 (val6Y1 b)
  | 3, 0 => pE6Y2 (val6Y4 e)
  | 3, 1 => pE6Y2 (val6Y7 h)
  | 3, 2 => pE6Y2 (val6Y6 g)
  | 3, 3 => pE6Y2 (val6Y5 f)
  | 3, 4 => pE6Y2 i
  | 3, 5 => pE6Y3 i
  | 4, 0 => pE6Y4 (val6Y6 g)
  | 4, 1 => pE6Y4 i
  | 4, 2 => pE6Y4 (val6Y4 e)
  | 4, 3 => pE6Y5 i
  | 4, 4 => pE6Y4 (val6Y5 f)
  | 4, 5 => pE6Y4 (val6Y7 h)
  | 5, 0 => pE6Y6 (val6Y6 g)
  | 5, 1 => pE6Y6 i
  | 5, 2 => pE6Y6 (val6Y4 e)
  | 5, 3 => pE6Y7 i
  | 5, 4 => pE6Y6 (val6Y7 h)
  | 5, 5 => pE6Y6 (val6Y5 f)

theorem tab6Y_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) :
    tab6Y a b c d e f g h i = Magma.transport permE6Y tr6Y (dec6Y a b c d e f g h i) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `98304` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6Y : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6Y 0 0 1 1 3 3 3 3 3
  | 1 => tab6Y 0 3 0 3 0 3 0 1 5

/-- The arguments as one mixed-radix index, which is how `rankIdx6Y` is addressed. -/
def encT6Y (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Nat :=
  a.1 * 49152 +
    b.1 * 12288 +
    c.1 * 6144 +
    d.1 * 1536 +
    e.1 * 384 +
    f.1 * 96 +
    g.1 * 24 +
    h.1 * 6 +
    i.1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6Y` can name one
rather than search the list for it. The `98302` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6Y` excludes them. Read only by `native_decide`. -/
def rankIdx6Y : Nat → Nat
  | 9213 => 0
  | 41771 => 1
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6Y (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 2 :=
  ⟨min (rankIdx6Y (encT6Y a b c d e f g h i)) 1, by omega⟩


/-- `2` of the `26` demanded maps and `3` of the `46630` forbidden ones, enough to separate the `2`
members from the other `98302` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6Y` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6Y : Fin 2 → Fin 26
  | 0 => 1
  | 1 => 4
def x0idx6Y : Fin 3 → Fin 46630
  | 0 => 5
  | 1 => 73
  | 2 => 891

def endE06Y (j : Fin 2) : Fin 6 → Fin 6 := endE6Y (e0idx6Y j)

def endX06Y (j : Fin 3) : Fin 6 → Fin 6 := endX6Y (x0idx6Y j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6Y (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6Y i)

theorem end6Y_isEndo (i : Fin 2) (j : Fin 26) : (end6Y i).IsEndo (endE6Y j) := by
  revert i j; native_decide

theorem end6Y_not_isEndo (i : Fin 2) (j : Fin 46630) : ¬ (end6Y i).IsEndo (endX6Y j) := by
  revert i j; native_decide

/-- `rank6Y` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6Y` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6Y (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6Y a b c d e f g h i) endE06Y endX06Y = true) :
    mem6Y (rank6Y a b c d e f g h i) = tab6Y a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6Y (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6Y a b c d e f g h i) endE06Y endX06Y = true) :
    ∃ idx, mem6Y idx = tab6Y a b c d e f g h i :=
  ⟨_, mem_rank6Y a b c d e f g h i hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6Y`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6Y` turns that into a member index. -/
theorem exists_end6Y {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6Y j))
    (hX : ∀ j, ¬ M.IsEndo (endX6Y j)) : ∃ i, end6Y i = M := by
  have hP : ∀ i, M.IsEndo (permE6Y i) := by
    intro i; rw [permE6Y_eq_endE6Y]; exact hE (uidx6Y i)
  have hop : M.op = Magma.transport permE6Y tr6Y (fun i ↦ M.op (rep6Y i).1 (rep6Y i).2) :=
    Magma.op_eq_transport (rep := rep6Y) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y0) (a := (rep6Y 0).1) (b := (rep6Y 0).2)
    (val := val6Y0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y1) (a := (rep6Y 1).1) (b := (rep6Y 1).2)
    (val := val6Y1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y2) (a := (rep6Y 2).1) (b := (rep6Y 2).2)
    (val := val6Y2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y3) (a := (rep6Y 3).1) (b := (rep6Y 3).2)
    (val := val6Y3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y4) (a := (rep6Y 4).1) (b := (rep6Y 4).2)
    (val := val6Y4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y5) (a := (rep6Y 5).1) (b := (rep6Y 5).2)
    (val := val6Y5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y6) (a := (rep6Y 6).1) (b := (rep6Y 6).2)
    (val := val6Y6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y7) (a := (rep6Y 7).1) (b := (rep6Y 7).2)
    (val := val6Y7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6Y) (idx := stabIdx6Y8) (a := (rep6Y 8).1) (b := (rep6Y 8).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6Y a b c d e f g h i = fun i ↦ M.op (rep6Y i).1 (rep6Y i).2 := by
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
  have key : tab6Y a b c d e f g h i = M.op := by
    rw [tab6Y_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6Y a b c d e f g h i) endE06Y endX06Y = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6Y j), fun j ↦ hX (x0idx6Y j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6Y a b c d e f g h i hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`26` monoid of `Magma.endE6Y`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6Y {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6Y i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6Y j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6Y i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6Y
    (fun k ↦ (Magma.end6Y_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6Y_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
