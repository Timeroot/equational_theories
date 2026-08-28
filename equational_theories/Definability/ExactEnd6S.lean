import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `S` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `6`: `⟨(0 1 2)(3 4 5), (1 2)(4 5)⟩`

`End(M)` is `30` maps, so `Aut(M)` -- its unit group -- is these `6` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `8` orbit values rather than `36`
independent cells. -/

/-- The `6` elements of the group: `()`, `(1 2)(4 5)`, `(0 1)(3 4)`, `(0 1 2)(3 4 5)`, `(0 2 1)(3 5
4)`, `(0 2)(3 5)`. -/
def pE6S0 : Fin 6 → Fin 6 := id
def pE6S1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pE6S2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5
def pE6S3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3
def pE6S4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4
def pE6S5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3

def permE6S : Fin 6 → Fin 6 → Fin 6
  | 0 => pE6S0
  | 1 => pE6S1
  | 2 => pE6S2
  | 3 => pE6S3
  | 4 => pE6S4
  | 5 => pE6S5

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `30` self-maps that must be endomorphisms: `333000`, `444111`, `555222`,
`000333`, `100433`, `200533`, `010343`, `110443`, `210543`, `020353`, `120453`, `220553`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6S : Fin 30 → Fin 46656
  | 0 => 129
  | 1 => 9460
  | 2 => 18791
  | 3 => 27864
  | 4 => 28081
  | 5 => 28298
  | 6 => 29166
  | 7 => 29383
  | 8 => 29600
  | 9 => 30468
  | 10 => 30685
  | 11 => 30902
  | 12 => 35676
  | 13 => 35893
  | 14 => 36110
  | 15 => 36978
  | 16 => 37195
  | 17 => 37412
  | 18 => 38280
  | 19 => 38497
  | 20 => 38714
  | 21 => 43488
  | 22 => 43705
  | 23 => 43922
  | 24 => 44790
  | 25 => 45007
  | 26 => 45224
  | 27 => 46092
  | 28 => 46309
  | _ => 46526

def endE6S (j : Fin 30) : Fin 6 → Fin 6 := allMaps6 (eidx6S j)

/-- Indices of the other `46626`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6S : Array Nat := #[
  129, 9460, 18791, 27864, 28081, 28298, 29166, 29383, 29600, 30468, 30685, 30902, 35676, 35893,
  36110, 36978, 37195, 37412, 38280, 38497, 38714, 43488, 43705, 43922, 44790, 45007, 45224,
  46092, 46309, 46526]

def xarr6S : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6S.contains i)

def xidx6S (j : Fin 46626) : Fin 46656 :=
  ⟨min (xarr6S.getD j.1 0) 46655, by omega⟩

def endX6S (j : Fin 46626) : Fin 6 → Fin 6 := allMaps6 (xidx6S j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6S` is given. -/
def uidx6S : Fin 6 → Fin 30
  | 0 => 24
  | 1 => 18
  | 2 => 22
  | 3 => 10
  | 4 => 14
  | 5 => 8

theorem permE6S_eq_endE6S (i : Fin 6) : permE6S i = endE6S (uidx6S i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `8`, so an invariant
operation is `8` values. -/
def rep6S : Fin 8 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (3, 0)
  | 5 => (3, 1)
  | 6 => (3, 3)
  | 7 => (3, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6S : Fin 6 → Fin 6 → Fin 8 × Fin 6
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
def stabIdx6S0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6S0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6S1 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6S2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6S2 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6S3 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6S4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6S4 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6S5 : Fin 1 → Fin 6
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `6`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6S6 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1
def val6S6 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `7`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6S7 : Fin 1 → Fin 6
  | 0 => 0

/-- The `8` orbit values named by the family's arguments. -/
def dec6S (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 8 → Fin 6
  | 0 => val6S0 a
  | 1 => b
  | 2 => val6S2 c
  | 3 => d
  | 4 => val6S4 e
  | 5 => f
  | 6 => val6S6 g
  | 7 => h

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6S_eq_transport`). -/
def tab6S (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6S0 a
  | 0, 1 => b
  | 0, 2 => pE6S1 b
  | 0, 3 => val6S2 c
  | 0, 4 => d
  | 0, 5 => pE6S1 d
  | 1, 0 => pE6S2 b
  | 1, 1 => pE6S2 (val6S0 a)
  | 1, 2 => pE6S3 b
  | 1, 3 => pE6S2 d
  | 1, 4 => pE6S2 (val6S2 c)
  | 1, 5 => pE6S3 d
  | 2, 0 => pE6S4 b
  | 2, 1 => pE6S5 b
  | 2, 2 => pE6S4 (val6S0 a)
  | 2, 3 => pE6S4 d
  | 2, 4 => pE6S5 d
  | 2, 5 => pE6S4 (val6S2 c)
  | 3, 0 => val6S4 e
  | 3, 1 => f
  | 3, 2 => pE6S1 f
  | 3, 3 => val6S6 g
  | 3, 4 => h
  | 3, 5 => pE6S1 h
  | 4, 0 => pE6S2 f
  | 4, 1 => pE6S2 (val6S4 e)
  | 4, 2 => pE6S3 f
  | 4, 3 => pE6S2 h
  | 4, 4 => pE6S2 (val6S6 g)
  | 4, 5 => pE6S3 h
  | 5, 0 => pE6S4 f
  | 5, 1 => pE6S5 f
  | 5, 2 => pE6S4 (val6S4 e)
  | 5, 3 => pE6S4 h
  | 5, 4 => pE6S5 h
  | 5, 5 => pE6S4 (val6S6 g)

theorem tab6S_eq_transport (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6) :
    tab6S a b c d e f g h = Magma.transport permE6S tr6S (dec6S a b c d e f g h) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `24` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one
index. Of the `20736` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def mem6S : Fin 24 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6S 1 3 0 0 1 3 0 1
  | 1 => tab6S 1 3 0 0 1 4 0 0
  | 2 => tab6S 1 3 0 0 1 4 0 1
  | 3 => tab6S 1 3 0 1 1 3 0 0
  | 4 => tab6S 1 3 0 1 1 3 0 1
  | 5 => tab6S 1 3 0 1 1 4 0 1
  | 6 => tab6S 1 3 1 3 0 0 0 1
  | 7 => tab6S 1 3 1 3 0 1 0 0
  | 8 => tab6S 1 3 1 3 0 1 0 1
  | 9 => tab6S 1 3 1 4 0 0 0 0
  | 10 => tab6S 1 3 1 4 0 0 0 1
  | 11 => tab6S 1 3 1 4 0 1 0 1
  | 12 => tab6S 1 4 0 0 1 3 0 0
  | 13 => tab6S 1 4 0 0 1 4 0 0
  | 14 => tab6S 1 4 0 0 1 4 0 1
  | 15 => tab6S 1 4 0 1 1 3 0 0
  | 16 => tab6S 1 4 0 1 1 3 0 1
  | 17 => tab6S 1 4 0 1 1 4 0 0
  | 18 => tab6S 1 4 1 3 0 0 0 0
  | 19 => tab6S 1 4 1 3 0 1 0 0
  | 20 => tab6S 1 4 1 3 0 1 0 1
  | 21 => tab6S 1 4 1 4 0 0 0 0
  | 22 => tab6S 1 4 1 4 0 0 0 1
  | _ => tab6S 1 4 1 4 0 1 0 0

/-- The arguments as one mixed-radix index, which is how `rankIdx6S` is addressed. -/
def encT6S (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Nat :=
  a.1 * 10368 +
    b.1 * 1728 +
    c.1 * 864 +
    d.1 * 144 +
    e.1 * 72 +
    f.1 * 12 +
    g.1 * 6 +
    h.1

/-- Which of the `24` members a given invariant tuple is, so that `mem_of_isExact6S` can name one
rather than search the list for it. The `20712` tuples that are not members fall through to `0`; the
hypothesis of `mem_rank6S` excludes them. Read only by `native_decide`. -/
def rankIdx6S : Nat → Nat
  | 15661 => 0
  | 15672 => 1
  | 15673 => 2
  | 15804 => 3
  | 15805 => 4
  | 15817 => 5
  | 16849 => 6
  | 16860 => 7
  | 16861 => 8
  | 16992 => 9
  | 16993 => 10
  | 17005 => 11
  | 17388 => 12
  | 17400 => 13
  | 17401 => 14
  | 17532 => 15
  | 17533 => 16
  | 17544 => 17
  | 18576 => 18
  | 18588 => 19
  | 18589 => 20
  | 18720 => 21
  | 18721 => 22
  | 18732 => 23
  | _ => 0

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6S (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6) (g : Fin 2)
    (h : Fin 6) : Fin 24 :=
  ⟨min (rankIdx6S (encT6S a b c d e f g h)) 23, by omega⟩


/-- `2` of the `30` demanded maps and `2` of the `46626` forbidden ones, enough to separate the `24`
members from the other `20712` invariant tuples between them. The certificate still demands and
forbids all `46656`; these are the lists `mem_rank6S` scans, once per tuple, with a scan that is
quadratic in their length. -/
def e0idx6S : Fin 2 → Fin 30
  | 0 => 0
  | 1 => 4
def x0idx6S : Fin 2 → Fin 46626
  | 0 => 0
  | 1 => 345

def endE06S (j : Fin 2) : Fin 6 → Fin 6 := endE6S (e0idx6S j)

def endX06S (j : Fin 2) : Fin 6 → Fin 6 := endX6S (x0idx6S j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6S (i : Fin 24) : Magma (Fin 6) := Magma.mk (mem6S i)

theorem end6S_isEndo (i : Fin 24) (j : Fin 30) : (end6S i).IsEndo (endE6S j) := by
  revert i j; native_decide

theorem end6S_not_isEndo (i : Fin 24) (j : Fin 46626) : ¬ (end6S i).IsEndo (endX6S j) := by
  revert i j; native_decide

/-- `rank6S` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6S` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6S (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6)
    (hx : Magma.isExact (tab6S a b c d e f g h) endE06S endX06S = true) :
    mem6S (rank6S a b c d e f g h) = tab6S a b c d e f g h := by
  revert hx; revert a b c d e f g h; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `24` listed
members. -/
theorem mem_of_isExact6S (a : Fin 2) (b : Fin 6) (c : Fin 2) (d : Fin 6) (e : Fin 2) (f : Fin 6)
    (g : Fin 2) (h : Fin 6)
    (hx : Magma.isExact (tab6S a b c d e f g h) endE06S endX06S = true) :
    ∃ idx, mem6S idx = tab6S a b c d e f g h :=
  ⟨_, mem_rank6S a b c d e f g h hx⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6S`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6S` turns that into a member index. -/
theorem exists_end6S {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6S j))
    (hX : ∀ j, ¬ M.IsEndo (endX6S j)) : ∃ i, end6S i = M := by
  have hP : ∀ i, M.IsEndo (permE6S i) := by
    intro i; rw [permE6S_eq_endE6S]; exact hE (uidx6S i)
  have hop : M.op = Magma.transport permE6S tr6S (fun i ↦ M.op (rep6S i).1 (rep6S i).2) :=
    Magma.op_eq_transport (rep := rep6S) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S0) (a := (rep6S 0).1) (b := (rep6S 0).2)
    (val := val6S0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S1) (a := (rep6S 1).1) (b := (rep6S 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S2) (a := (rep6S 2).1) (b := (rep6S 2).2)
    (val := val6S2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S3) (a := (rep6S 3).1) (b := (rep6S 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S4) (a := (rep6S 4).1) (b := (rep6S 4).2)
    (val := val6S4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S5) (a := (rep6S 5).1) (b := (rep6S 5).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨g, hg⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S6) (a := (rep6S 6).1) (b := (rep6S 6).2)
    (val := val6S6) hP (by decide) (by decide)
  obtain ⟨h, hh⟩ := Magma.exists_val_of_isEndo
    (E := permE6S) (idx := stabIdx6S7) (a := (rep6S 7).1) (b := (rep6S 7).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec6S a b c d e f g h = fun i ↦ M.op (rep6S i).1 (rep6S i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · exact hg
    · exact hh
  have key : tab6S a b c d e f g h = M.op := by
    rw [tab6S_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6S a b c d e f g h) endE06S endX06S = true := by
    rw [key, Magma.isExact_iff]; exact ⟨fun j ↦ hE (e0idx6S j), fun j ↦ hX (x0idx6S j)⟩
  obtain ⟨idx, hidx⟩ := mem_of_isExact6S a b c d e f g h hok
  exact ⟨idx, (congrArg Magma.mk (hidx.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`30` monoid of `Magma.endE6S`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6S {L L' : Law.NatMagmaLaw} {i : Fin 24}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6S i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6S j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6S i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6S
    (fun k ↦ (Magma.end6S_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6S_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
