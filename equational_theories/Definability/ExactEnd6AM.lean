import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `AM` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 2)(1 4)(3 5), (0 2)(1 4 3 5)⟩`

`End(M)` is `20` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `9` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(4 5)`, `(1 3)`, `(1 3)(4 5)`, `(0 2)(1 4)(3 5)`, `(0 2)(1
4 3 5)`, `(0 2)(1 5 3 4)`, `(0 2)(1 5)(3 4)`. -/
def pE6AM0 : Fin 6 → Fin 6 := id
def pE6AM1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pE6AM2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5
def pE6AM3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4
def pE6AM4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 3
def pE6AM5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 5 | 4 => 3 | 5 => 1
def pE6AM6 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 3
def pE6AM7 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1

def permE6AM : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6AM0
  | 1 => pE6AM1
  | 2 => pE6AM2
  | 3 => pE6AM3
  | 4 => pE6AM4
  | 5 => pE6AM5
  | 6 => pE6AM6
  | 7 => pE6AM7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `20` self-maps that must be endomorphisms: `000000`, `220200`, `240400`,
`250500`, `220211`, `250431`, `240531`, `002022`, `012122`, `222222`, `032322`, `250413`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6AM : Fin 20 → Fin 46656
  | 0 => 0
  | 1 => 446
  | 2 => 890
  | 3 => 1112
  | 4 => 9518
  | 5 => 12560
  | 6 => 12770
  | 7 => 18216
  | 8 => 18438
  | 9 => 18662
  | 10 => 18882
  | 11 => 25520
  | 12 => 25730
  | 13 => 27662
  | 14 => 36360
  | 15 => 37890
  | 16 => 38310
  | 17 => 44370
  | 18 => 44790
  | _ => 45432

def endE6AM (j : Fin 20) : Fin 6 → Fin 6 := allMaps6 (eidx6AM j)

/-- Indices of the other `46636`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6AM : Array Nat := #[
  0, 446, 890, 1112, 9518, 12560, 12770, 18216, 18438, 18662, 18882, 25520, 25730, 27662, 36360,
  37890, 38310, 44370, 44790, 45432]

def xarr6AM : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6AM.contains i)

def xidx6AM (j : Fin 46636) : Fin 46656 :=
  ⟨min (xarr6AM.getD j.1 0) 46655, by omega⟩

def endX6AM (j : Fin 46636) : Fin 6 → Fin 6 := allMaps6 (xidx6AM j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6AM` is given. -/
def uidx6AM : Fin 8 → Fin 20
  | 0 => 18
  | 1 => 16
  | 2 => 17
  | 3 => 15
  | 4 => 12
  | 5 => 6
  | 6 => 11
  | 7 => 5

theorem permE6AM_eq_endE6AM (i : Fin 8) : permE6AM i = endE6AM (uidx6AM i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `9`, so an invariant
operation is `9` values. -/
def rep6AM : Fin 9 → Fin 6 × Fin 6
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
def tr6AM : Fin 6 → Fin 6 → Fin 9 × Fin 8
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
def stabIdx6AM0 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6AM0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AM1 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AM1 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `4` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6AM2 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6AM2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `2`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AM3 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 2
def val6AM3 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AM4 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AM4 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AM5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AM5 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AM6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AM6 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `3`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6AM7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 1
def val6AM7 : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The one group element fixing both coordinates of orbit `8`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6AM8 : Fin 1 → Fin 8
  | 0 => 0

/-- The `9` orbit values named by the family's arguments. -/
def dec6AM (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 9 → Fin 6
  | 0 => val6AM0 a
  | 1 => val6AM1 b
  | 2 => val6AM2 c
  | 3 => val6AM3 d
  | 4 => val6AM4 e
  | 5 => val6AM5 f
  | 6 => val6AM6 g
  | 7 => val6AM7 h
  | 8 => i

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6AM_eq_transport`). -/
def tab6AM (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6AM0 a
  | 0, 1 => val6AM1 b
  | 0, 2 => val6AM2 c
  | 0, 3 => pE6AM2 (val6AM1 b)
  | 0, 4 => val6AM3 d
  | 0, 5 => pE6AM1 (val6AM3 d)
  | 1, 0 => val6AM4 e
  | 1, 1 => val6AM5 f
  | 1, 2 => val6AM6 g
  | 1, 3 => val6AM7 h
  | 1, 4 => i
  | 1, 5 => pE6AM1 i
  | 2, 0 => pE6AM4 (val6AM2 c)
  | 2, 1 => pE6AM4 (val6AM3 d)
  | 2, 2 => pE6AM4 (val6AM0 a)
  | 2, 3 => pE6AM5 (val6AM3 d)
  | 2, 4 => pE6AM4 (val6AM1 b)
  | 2, 5 => pE6AM6 (val6AM1 b)
  | 3, 0 => pE6AM2 (val6AM4 e)
  | 3, 1 => pE6AM2 (val6AM7 h)
  | 3, 2 => pE6AM2 (val6AM6 g)
  | 3, 3 => pE6AM2 (val6AM5 f)
  | 3, 4 => pE6AM2 i
  | 3, 5 => pE6AM3 i
  | 4, 0 => pE6AM4 (val6AM6 g)
  | 4, 1 => pE6AM4 i
  | 4, 2 => pE6AM4 (val6AM4 e)
  | 4, 3 => pE6AM5 i
  | 4, 4 => pE6AM4 (val6AM5 f)
  | 4, 5 => pE6AM4 (val6AM7 h)
  | 5, 0 => pE6AM6 (val6AM6 g)
  | 5, 1 => pE6AM6 i
  | 5, 2 => pE6AM6 (val6AM4 e)
  | 5, 3 => pE6AM7 i
  | 5, 4 => pE6AM6 (val6AM7 h)
  | 5, 5 => pE6AM6 (val6AM5 f)

theorem tab6AM_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) :
    tab6AM a b c d e f g h i = Magma.transport permE6AM tr6AM (dec6AM a b c d e f g h i) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `6` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `98304` invariant tuples these are the ones the forbidden maps rule out; naming only them
keeps the exactness test off the hot path of a family scan. -/
def mem6AM : Fin 6 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6AM 0 0 0 0 0 0 1 0 3
  | 1 => tab6AM 0 0 1 2 0 0 2 0 5
  | 2 => tab6AM 0 0 1 2 1 0 2 0 5
  | 3 => tab6AM 0 1 0 0 0 0 1 0 3
  | 4 => tab6AM 0 1 0 0 1 0 1 0 3
  | 5 => tab6AM 0 1 1 2 1 0 2 0 5

/-- The arguments as one mixed-radix index, which is how `rankIdx6AM` is addressed. -/
def encT6AM (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Nat :=
  a.1 * 49152 +
    b.1 * 12288 +
    c.1 * 6144 +
    d.1 * 1536 +
    e.1 * 384 +
    f.1 * 96 +
    g.1 * 24 +
    h.1 * 6 +
    i.1

/-- Which of the `6` members a given invariant tuple is, so that `mem_of_isExact6AM` can name one
rather than search the list for it. The `98298` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6AM` excludes them. Read only by `native_decide`. -/
def rankIdx6AM : Nat → Nat
  | 27 => 0
  | 9269 => 1
  | 9653 => 2
  | 12315 => 3
  | 12699 => 4
  | 21941 => 5
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6AM (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6) : Fin 6 :=
  ⟨min (rankIdx6AM (encT6AM a b c d e f g h i)) 5, by omega⟩


/-- `2` of the `20` demanded maps and `3` of the `46636` forbidden ones, enough to separate the `6`
members from the other `98298` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6AM` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6AM : Fin 2 → Fin 20
  | 0 => 0
  | 1 => 2
def x0idx6AM : Fin 3 → Fin 46636
  | 0 => 221
  | 1 => 889
  | 2 => 893

def endE06AM (j : Fin 2) : Fin 6 → Fin 6 := endE6AM (e0idx6AM j)

def endX06AM (j : Fin 3) : Fin 6 → Fin 6 := endX6AM (x0idx6AM j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6AM (i : Fin 6) : Magma (Fin 6) := Magma.mk (mem6AM i)

theorem end6AM_isEndo (i : Fin 6) (j : Fin 20) : (end6AM i).IsEndo (endE6AM j) := by
  revert i j; native_decide

theorem end6AM_not_isEndo (i : Fin 6) (j : Fin 46636) : ¬ (end6AM i).IsEndo (endX6AM j) := by
  revert i j; native_decide

/-- `rank6AM` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6AM` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6AM (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6AM a b c d e f g h i) endE06AM endX06AM = true) :
    mem6AM (rank6AM a b c d e f g h i) = tab6AM a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `6` listed
members. -/
theorem mem_of_isExact6AM (a : Fin 2) (b : Fin 4) (c : Fin 2) (d e f g h : Fin 4) (i : Fin 6)
    (hx : Magma.isExact (tab6AM a b c d e f g h i) endE06AM endX06AM = true) :
    ∃ idx, mem6AM idx = tab6AM a b c d e f g h i :=
  ⟨_, mem_rank6AM a b c d e f g h i hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6AM`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6AM` turns that into a member index. -/
theorem exists_end6AM {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6AM j))
    (hX : ∀ j, ¬ M.IsEndo (endX6AM j)) : ∃ i, end6AM i = M := by
  have hP : ∀ i, M.IsEndo (permE6AM i) := by
    intro i; rw [permE6AM_eq_endE6AM]; exact hE (uidx6AM i)
  have hop : M.op = Magma.transport permE6AM tr6AM (fun i ↦ M.op (rep6AM i).1 (rep6AM i).2) :=
    Magma.op_eq_transport (rep := rep6AM) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM0) (a := (rep6AM 0).1) (b := (rep6AM 0).2)
    (val := val6AM0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM1) (a := (rep6AM 1).1) (b := (rep6AM 1).2)
    (val := val6AM1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM2) (a := (rep6AM 2).1) (b := (rep6AM 2).2)
    (val := val6AM2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM3) (a := (rep6AM 3).1) (b := (rep6AM 3).2)
    (val := val6AM3) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM4) (a := (rep6AM 4).1) (b := (rep6AM 4).2)
    (val := val6AM4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM5) (a := (rep6AM 5).1) (b := (rep6AM 5).2)
    (val := val6AM5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM6) (a := (rep6AM 6).1) (b := (rep6AM 6).2)
    (val := val6AM6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM7) (a := (rep6AM 7).1) (b := (rep6AM 7).2)
    (val := val6AM7) hP (by decide) (by decide)
  obtain ⟨i, hi⟩ := Magma.exists_val_of_isEndo
    (E := permE6AM) (idx := stabIdx6AM8) (a := (rep6AM 8).1) (b := (rep6AM 8).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6AM a b c d e f g h i = fun i ↦ M.op (rep6AM i).1 (rep6AM i).2 := by
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
  have key : tab6AM a b c d e f g h i = M.op := by
    rw [tab6AM_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6AM a b c d e f g h i) endE06AM endX06AM = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6AM j), fun j ↦ hX (x0idx6AM j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6AM a b c d e f g h i hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`20` monoid of `Magma.endE6AM`, and no such magma satisfies `L`, then
`L` is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6AM {L L' : Law.NatMagmaLaw} {i : Fin 6}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6AM i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6AM j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6AM i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6AM
    (fun k ↦ (Magma.end6AM_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6AM_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
