import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `W` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `8`: `⟨(0 1)(2 3)(4 5), (0 1)(2 4 3 5)⟩`

`End(M)` is `32` maps, so `Aut(M)` -- its unit group -- is these `8` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `8` orbit values rather than `36`
independent cells. -/

/-- The `8` elements of the group: `()`, `(2 3)(4 5)`, `(2 4 3 5)`, `(2 5 3 4)`, `(0 1)`, `(0 1)(2
3)(4 5)`, `(0 1)(2 4 3 5)`, `(0 1)(2 5 3 4)`. -/
def pE6W0 : Fin 6 → Fin 6 := id
def pE6W1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6W2 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
def pE6W3 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3
def pE6W4 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pE6W5 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6W6 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
def pE6W7 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3

def permE6W : Fin 8 → Fin 6 → Fin 6
  | 0 => pE6W0
  | 1 => pE6W1
  | 2 => pE6W2
  | 3 => pE6W3
  | 4 => pE6W4
  | 5 => pE6W5
  | 6 => pE6W6
  | 7 => pE6W7

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `32` self-maps that must be endomorphisms: `000000`, `100000`, `010000`,
`110000`, `001100`, `101100`, `011100`, `111100`, `000011`, `100011`, `010011`, `110011`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6W : Fin 32 → Fin 46656
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
  | 4 => 252
  | 5 => 253
  | 6 => 258
  | 7 => 259
  | 8 => 9072
  | 9 => 9073
  | 10 => 9078
  | 11 => 9079
  | 12 => 9324
  | 13 => 9325
  | 14 => 9330
  | 15 => 9331
  | 16 => 20664
  | 17 => 20665
  | 18 => 20670
  | 19 => 20671
  | 20 => 26964
  | 21 => 26965
  | 22 => 26970
  | 23 => 26971
  | 24 => 38124
  | 25 => 38125
  | 26 => 38130
  | 27 => 38131
  | 28 => 44784
  | 29 => 44785
  | 30 => 44790
  | _ => 44791

def endE6W (j : Fin 32) : Fin 6 → Fin 6 := allMaps6 (eidx6W j)

/-- Indices of the other `46624`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6W : Array Nat := #[
  0, 1, 6, 7, 252, 253, 258, 259, 9072, 9073, 9078, 9079, 9324, 9325, 9330, 9331, 20664, 20665,
  20670, 20671, 26964, 26965, 26970, 26971, 38124, 38125, 38130, 38131, 44784, 44785, 44790, 44791]

def xarr6W : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6W.contains i)

def xidx6W (j : Fin 46624) : Fin 46656 :=
  ⟨min (xarr6W.getD j.1 0) 46655, by omega⟩

def endX6W (j : Fin 46624) : Fin 6 → Fin 6 := allMaps6 (xidx6W j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6W` is given. -/
def uidx6W : Fin 8 → Fin 32
  | 0 => 30
  | 1 => 26
  | 2 => 18
  | 3 => 22
  | 4 => 29
  | 5 => 25
  | 6 => 17
  | 7 => 21

theorem permE6W_eq_endE6W (i : Fin 8) : permE6W i = endE6W (uidx6W i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `8`, so an invariant
operation is `8` values. -/
def rep6W : Fin 8 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (2, 0)
  | 4 => (2, 2)
  | 5 => (2, 3)
  | 6 => (2, 4)
  | 7 => (2, 5)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6W : Fin 6 → Fin 6 → Fin 8 × Fin 8
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (2, 1)
  | 0, 4 => (2, 2)
  | 0, 5 => (2, 3)
  | 1, 0 => (1, 4)
  | 1, 1 => (0, 4)
  | 1, 2 => (2, 4)
  | 1, 3 => (2, 5)
  | 1, 4 => (2, 6)
  | 1, 5 => (2, 7)
  | 2, 0 => (3, 0)
  | 2, 1 => (3, 4)
  | 2, 2 => (4, 0)
  | 2, 3 => (5, 0)
  | 2, 4 => (6, 0)
  | 2, 5 => (7, 0)
  | 3, 0 => (3, 1)
  | 3, 1 => (3, 5)
  | 3, 2 => (5, 1)
  | 3, 3 => (4, 1)
  | 3, 4 => (7, 1)
  | 3, 5 => (6, 1)
  | 4, 0 => (3, 2)
  | 4, 1 => (3, 6)
  | 4, 2 => (7, 2)
  | 4, 3 => (6, 2)
  | 4, 4 => (4, 2)
  | 4, 5 => (5, 2)
  | 5, 0 => (3, 3)
  | 5, 1 => (3, 7)
  | 5, 2 => (6, 3)
  | 5, 3 => (7, 3)
  | 5, 4 => (5, 3)
  | 5, 5 => (4, 3)

/-- The `4` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6W0 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6W0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6W1 : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def val6W1 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6W2 : Fin 1 → Fin 8
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6W3 : Fin 1 → Fin 8
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6W4 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 4
def val6W4 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6W5 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 4
def val6W5 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6W6 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 4
def val6W6 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `2` group elements fixing both coordinates of orbit `7`'s representative, and hence its
value: that value must be one of `2`, `3`, `4`, `5`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdx6W7 : Fin 2 → Fin 8
  | 0 => 0
  | 1 => 4
def val6W7 : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The `8` orbit values named by the family's arguments. -/
def dec6W (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4) : Fin 8 → Fin 6
  | 0 => val6W0 a
  | 1 => val6W1 b
  | 2 => c
  | 3 => d
  | 4 => val6W4 e
  | 5 => val6W5 f
  | 6 => val6W6 g
  | 7 => val6W7 h

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6W_eq_transport`). -/
def tab6W (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6W0 a
  | 0, 1 => val6W1 b
  | 0, 2 => c
  | 0, 3 => pE6W1 c
  | 0, 4 => pE6W2 c
  | 0, 5 => pE6W3 c
  | 1, 0 => pE6W4 (val6W1 b)
  | 1, 1 => pE6W4 (val6W0 a)
  | 1, 2 => pE6W4 c
  | 1, 3 => pE6W5 c
  | 1, 4 => pE6W6 c
  | 1, 5 => pE6W7 c
  | 2, 0 => d
  | 2, 1 => pE6W4 d
  | 2, 2 => val6W4 e
  | 2, 3 => val6W5 f
  | 2, 4 => val6W6 g
  | 2, 5 => val6W7 h
  | 3, 0 => pE6W1 d
  | 3, 1 => pE6W5 d
  | 3, 2 => pE6W1 (val6W5 f)
  | 3, 3 => pE6W1 (val6W4 e)
  | 3, 4 => pE6W1 (val6W7 h)
  | 3, 5 => pE6W1 (val6W6 g)
  | 4, 0 => pE6W2 d
  | 4, 1 => pE6W6 d
  | 4, 2 => pE6W2 (val6W7 h)
  | 4, 3 => pE6W2 (val6W6 g)
  | 4, 4 => pE6W2 (val6W4 e)
  | 4, 5 => pE6W2 (val6W5 f)
  | 5, 0 => pE6W3 d
  | 5, 1 => pE6W7 d
  | 5, 2 => pE6W3 (val6W6 g)
  | 5, 3 => pE6W3 (val6W7 h)
  | 5, 4 => pE6W3 (val6W5 f)
  | 5, 5 => pE6W3 (val6W4 e)

theorem tab6W_eq_transport (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4) :
    tab6W a b c d e f g h = Magma.transport permE6W tr6W (dec6W a b c d e f g h) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `16` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `36864` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6W : Fin 16 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6W 0 0 0 2 1 0 0 1
  | 1 => tab6W 0 0 0 2 1 0 1 0
  | 2 => tab6W 0 0 0 2 1 1 0 1
  | 3 => tab6W 0 0 0 2 1 1 1 0
  | 4 => tab6W 0 0 0 3 1 0 0 1
  | 5 => tab6W 0 0 0 3 1 0 1 0
  | 6 => tab6W 0 0 0 3 1 1 0 1
  | 7 => tab6W 0 0 0 3 1 1 1 0
  | 8 => tab6W 0 1 2 0 1 0 2 2
  | 9 => tab6W 0 1 2 0 1 0 3 3
  | 10 => tab6W 0 1 2 0 1 1 2 2
  | 11 => tab6W 0 1 2 0 1 1 3 3
  | 12 => tab6W 0 1 3 0 1 0 2 2
  | 13 => tab6W 0 1 3 0 1 0 3 3
  | 14 => tab6W 0 1 3 0 1 1 2 2
  | _ => tab6W 0 1 3 0 1 1 3 3

/-- The arguments as one mixed-radix index, which is how `rankIdx6W` is addressed. -/
def encT6W (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4) : Nat :=
  a.1 * 18432 +
    b.1 * 9216 +
    c.1 * 1536 +
    d.1 * 256 +
    e.1 * 64 +
    f.1 * 16 +
    g.1 * 4 +
    h.1

/-- Which of the `16` members a given invariant tuple is, so that `mem_of_isExact6W` can name one
rather than search the list for it. The `36848` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6W` excludes them. Read only by `native_decide`. -/
def rankIdx6W : Nat → Nat
  | 577 => 0
  | 580 => 1
  | 593 => 2
  | 596 => 3
  | 833 => 4
  | 836 => 5
  | 849 => 6
  | 852 => 7
  | 12362 => 8
  | 12367 => 9
  | 12378 => 10
  | 12383 => 11
  | 13898 => 12
  | 13903 => 13
  | 13914 => 14
  | 13919 => 15
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6W (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4) : Fin 16 :=
  ⟨min (rankIdx6W (encT6W a b c d e f g h)) 15, by omega⟩


/-- `2` of the `32` demanded maps and `2` of the `46624` forbidden ones, enough to separate the `16`
members from the other `36848` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6W` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6W : Fin 2 → Fin 32
  | 0 => 1
  | 1 => 4
def x0idx6W : Fin 2 → Fin 46624
  | 0 => 18646
  | 1 => 20468

def endE06W (j : Fin 2) : Fin 6 → Fin 6 := endE6W (e0idx6W j)

def endX06W (j : Fin 2) : Fin 6 → Fin 6 := endX6W (x0idx6W j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6W (i : Fin 16) : Magma (Fin 6) := Magma.mk (mem6W i)

theorem end6W_isEndo (i : Fin 16) (j : Fin 32) : (end6W i).IsEndo (endE6W j) := by
  revert i j; native_decide

theorem end6W_not_isEndo (i : Fin 16) (j : Fin 46624) : ¬ (end6W i).IsEndo (endX6W j) := by
  revert i j; native_decide

/-- `rank6W` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6W` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6W (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4)
    (hx : Magma.isExact (tab6W a b c d e f g h) endE06W endX06W = true) :
    mem6W (rank6W a b c d e f g h) = tab6W a b c d e f g h := by
  revert hx; revert a b c d e f g h; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `16` listed
members. -/
theorem mem_of_isExact6W (a b : Fin 2) (c d : Fin 6) (e f g h : Fin 4)
    (hx : Magma.isExact (tab6W a b c d e f g h) endE06W endX06W = true) :
    ∃ idx, mem6W idx = tab6W a b c d e f g h :=
  ⟨_, mem_rank6W a b c d e f g h hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6W`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6W` turns that into a member index. -/
theorem exists_end6W {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6W j))
    (hX : ∀ j, ¬ M.IsEndo (endX6W j)) : ∃ i, end6W i = M := by
  have hP : ∀ i, M.IsEndo (permE6W i) := by
    intro i; rw [permE6W_eq_endE6W]; exact hE (uidx6W i)
  have hop : M.op = Magma.transport permE6W tr6W (fun i ↦ M.op (rep6W i).1 (rep6W i).2) :=
    Magma.op_eq_transport (rep := rep6W) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W0) (a := (rep6W 0).1) (b := (rep6W 0).2)
    (val := val6W0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W1) (a := (rep6W 1).1) (b := (rep6W 1).2)
    (val := val6W1) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W2) (a := (rep6W 2).1) (b := (rep6W 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W3) (a := (rep6W 3).1) (b := (rep6W 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W4) (a := (rep6W 4).1) (b := (rep6W 4).2)
    (val := val6W4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W5) (a := (rep6W 5).1) (b := (rep6W 5).2)
    (val := val6W5) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W6) (a := (rep6W 6).1) (b := (rep6W 6).2)
    (val := val6W6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6W) (idx := stabIdx6W7) (a := (rep6W 7).1) (b := (rep6W 7).2)
    (val := val6W7) hP (by decide) (by decide)
  have hdec : dec6W a b c d e f g h = fun i ↦ M.op (rep6W i).1 (rep6W i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
  have key : tab6W a b c d e f g h = M.op := by
    rw [tab6W_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6W a b c d e f g h) endE06W endX06W = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6W j), fun j ↦ hX (x0idx6W j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6W a b c d e f g h hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`32` monoid of `Magma.endE6W`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6W {L L' : Law.NatMagmaLaw} {i : Fin 16}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6W i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6W j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6W i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6W
    (fun k ↦ (Magma.end6W_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6W_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
