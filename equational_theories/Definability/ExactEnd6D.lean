import equational_theories.Definability.ExactEnd6

/-!
# The exact-endomorphism class `D` on `Fin 6`

One class of `Definability/ExactEnd6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `12`: `⟨(0 1)(2 3)(4 5), (0 1 2 4 5 3)⟩`

`End(M)` is `36` maps, so `Aut(M)` -- its unit group -- is these `12` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `36`
independent cells. -/

/-- The `12` elements of the group: `()`, `(1 3)(2 5)`, `(0 1)(2 3)(4 5)`, `(0 1 2 4 5 3)`, `(0 2)(3
4)`, `(0 2 5)(1 4 3)`, `(0 3 5 4 2 1)`, `(0 3)(1 5)(2 4)`, `(0 4)(1 2)(3 5)`, `(0 4)(1 5)(2 3)`, `(0
5 2)(1 3 4)`, `(0 5)(1 4)`. -/
def pE6D0 : Fin 6 → Fin 6 := id
def pE6D1 : Fin 6 → Fin 6 | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 4 | 5 => 2
def pE6D2 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pE6D3 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 3
def pE6D4 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5
def pE6D5 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 0
def pE6D6 : Fin 6 → Fin 6 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 4
def pE6D7 : Fin 6 → Fin 6 | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 1
def pE6D8 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 0 | 5 => 3
def pE6D9 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 1
def pE6D10 : Fin 6 → Fin 6 | 0 => 5 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 2
def pE6D11 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 0

def permE6D : Fin 12 → Fin 6 → Fin 6
  | 0 => pE6D0
  | 1 => pE6D1
  | 2 => pE6D2
  | 3 => pE6D3
  | 4 => pE6D4
  | 5 => pE6D5
  | 6 => pE6D6
  | 7 => pE6D7
  | 8 => pE6D8
  | 9 => pE6D9
  | 10 => pE6D10
  | 11 => pE6D11

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `46656` self-maps of `Fin 6`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps6` indexes the self-maps, digit by digit. -/

/-- Indices of the `36` self-maps that must be endomorphisms: `000000`, `542310`, `020220`,
`245130`, `040440`, `050550`, `453201`, `111111`, `354021`, `131331`, `141441`, `151551`, ... (each
written as its list of values at `0, 1, ..., 5`). -/
def eidx6D : Fin 36 → Fin 46656
  | 0 => 0
  | 1 => 2045
  | 2 => 3036
  | 3 => 4310
  | 4 => 6072
  | 5 => 7590
  | 6 => 8350
  | 7 => 9331
  | 8 => 10545
  | 9 => 12367
  | 10 => 13885
  | 11 => 15403
  | 12 => 15626
  | 13 => 17735
  | 14 => 18662
  | 15 => 20180
  | 16 => 21150
  | 17 => 23216
  | 18 => 24460
  | 19 => 24957
  | 20 => 26475
  | 21 => 27993
  | 22 => 29511
  | 23 => 29965
  | 24 => 31252
  | 25 => 32770
  | 26 => 34815
  | 27 => 35806
  | 28 => 37324
  | 29 => 38125
  | 30 => 39065
  | 31 => 40583
  | 32 => 42101
  | 33 => 43640
  | 34 => 44790
  | _ => 46655

def endE6D (j : Fin 36) : Fin 6 → Fin 6 := allMaps6 (eidx6D j)

/-- Indices of the other `46620`, which must not be endomorphisms, reached through the complement.
Neither this nor `xidx` is ever evaluated by the kernel: `endX` occurs only in `native_decide` goals
and under `Magma.isExact_iff`, which is a rewrite. -/
def eset6D : Array Nat := #[
  0, 2045, 3036, 4310, 6072, 7590, 8350, 9331, 10545, 12367, 13885, 15403, 15626, 17735, 18662,
  20180, 21150, 23216, 24460, 24957, 26475, 27993, 29511, 29965, 31252, 32770, 34815, 35806,
  37324, 38125, 39065, 40583, 42101, 43640, 44790, 46655]

def xarr6D : Array Nat :=
  (Array.range 46656).filter (fun i => !eset6D.contains i)

def xidx6D (j : Fin 46620) : Fin 46656 :=
  ⟨min (xarr6D.getD j.1 0) 46655, by omega⟩

def endX6D (j : Fin 46620) : Fin 6 → Fin 6 := allMaps6 (xidx6D j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end6D` is given. -/
def uidx6D : Fin 12 → Fin 36
  | 0 => 34
  | 1 => 16
  | 2 => 29
  | 3 => 23
  | 4 => 33
  | 5 => 3
  | 6 => 26
  | 7 => 8
  | 8 => 18
  | 9 => 6
  | 10 => 13
  | 11 => 1

theorem permE6D_eq_endE6D (i : Fin 12) : permE6D i = endE6D (uidx6D i) := by
  revert i; decide

/-- One representative per orbit of the group on the `36` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep6D : Fin 4 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 4)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr6D : Fin 6 → Fin 6 → Fin 4 × Fin 12
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (1, 1)
  | 0, 4 => (3, 0)
  | 0, 5 => (2, 1)
  | 1, 0 => (1, 2)
  | 1, 1 => (0, 2)
  | 1, 2 => (1, 3)
  | 1, 3 => (2, 2)
  | 1, 4 => (2, 3)
  | 1, 5 => (3, 2)
  | 2, 0 => (2, 4)
  | 2, 1 => (1, 4)
  | 2, 2 => (0, 4)
  | 2, 3 => (3, 4)
  | 2, 4 => (1, 5)
  | 2, 5 => (2, 5)
  | 3, 0 => (1, 6)
  | 3, 1 => (2, 6)
  | 3, 2 => (3, 6)
  | 3, 3 => (0, 6)
  | 3, 4 => (2, 7)
  | 3, 5 => (1, 7)
  | 4, 0 => (3, 8)
  | 4, 1 => (2, 8)
  | 4, 2 => (1, 8)
  | 4, 3 => (2, 9)
  | 4, 4 => (0, 8)
  | 4, 5 => (1, 9)
  | 5, 0 => (2, 10)
  | 5, 1 => (3, 10)
  | 5, 2 => (2, 11)
  | 5, 3 => (1, 10)
  | 5, 4 => (1, 11)
  | 5, 5 => (0, 10)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6D0 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6D0 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 4

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6D1 : Fin 1 → Fin 12
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 6`. -/
def stabIdx6D2 : Fin 1 → Fin 12
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `4`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx6D3 : Fin 2 → Fin 12
  | 0 => 0
  | 1 => 1
def val6D3 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 4

/-- The `4` orbit values named by the family's arguments. -/
def dec6D (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 4 → Fin 6
  | 0 => val6D0 a
  | 1 => b
  | 2 => c
  | 3 => val6D3 d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab6D_eq_transport`). -/
def tab6D (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => val6D0 a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => pE6D1 b
  | 0, 4 => val6D3 d
  | 0, 5 => pE6D1 c
  | 1, 0 => pE6D2 b
  | 1, 1 => pE6D2 (val6D0 a)
  | 1, 2 => pE6D3 b
  | 1, 3 => pE6D2 c
  | 1, 4 => pE6D3 c
  | 1, 5 => pE6D2 (val6D3 d)
  | 2, 0 => pE6D4 c
  | 2, 1 => pE6D4 b
  | 2, 2 => pE6D4 (val6D0 a)
  | 2, 3 => pE6D4 (val6D3 d)
  | 2, 4 => pE6D5 b
  | 2, 5 => pE6D5 c
  | 3, 0 => pE6D6 b
  | 3, 1 => pE6D6 c
  | 3, 2 => pE6D6 (val6D3 d)
  | 3, 3 => pE6D6 (val6D0 a)
  | 3, 4 => pE6D7 c
  | 3, 5 => pE6D7 b
  | 4, 0 => pE6D8 (val6D3 d)
  | 4, 1 => pE6D8 c
  | 4, 2 => pE6D8 b
  | 4, 3 => pE6D9 c
  | 4, 4 => pE6D8 (val6D0 a)
  | 4, 5 => pE6D9 b
  | 5, 0 => pE6D10 c
  | 5, 1 => pE6D10 (val6D3 d)
  | 5, 2 => pE6D11 c
  | 5, 3 => pE6D10 b
  | 5, 4 => pE6D11 b
  | 5, 5 => pE6D10 (val6D0 a)

theorem tab6D_eq_transport (a : Fin 2) (b c : Fin 6) (d : Fin 2) :
    tab6D a b c d = Magma.transport permE6D tr6D (dec6D a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 6` whose endomorphism monoid is exactly this one, listed under one index.
Of the `144` invariant tuples these are the ones the forbidden maps rule out; naming only them keeps
the exactness test off the hot path of a family scan. -/
def mem6D : Fin 2 → Fin 6 → Fin 6 → Fin 6
  | 0 => tab6D 0 2 0 0
  | 1 => tab6D 0 3 2 1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact6D` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr6D : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr6D` is addressed. -/
def encT6D (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Nat :=
  a.1 * 72 +
    b.1 * 12 +
    c.1 * 2 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank6D (a : Fin 2) (b c : Fin 6) (d : Fin 2) : Fin 2 :=
  ⟨min (rankArr6D.getD (encT6D a b c d) 0) 1, by omega⟩


/-- `1` of the `46620` forbidden maps, enough to separate the `2` members from the other `142`
invariant tuples on their own. The certificate still forbids all `46620`; this is the list
`mem_rank6D` scans, and scanning is quadratic. -/
def x0idx6D : Fin 1 → Fin 46620
  | 0 => 1720

def endX06D (j : Fin 1) : Fin 6 → Fin 6 := endX6D (x0idx6D j)

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end6D (i : Fin 2) : Magma (Fin 6) := Magma.mk (mem6D i)

theorem end6D_isEndo (i : Fin 2) (j : Fin 36) : (end6D i).IsEndo (endE6D j) := by
  revert i j; native_decide

theorem end6D_not_isEndo (i : Fin 2) (j : Fin 46620) : ¬ (end6D i).IsEndo (endX6D j) := by
  revert i j; native_decide

/-- `rank6D` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem6D` for the index would be a comparison per tuple and
member. -/
theorem mem_rank6D (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tab6D a b c d) endE6D endX06D = true) :
    mem6D (rank6D a b c d) = tab6D a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact6D (a : Fin 2) (b c : Fin 6) (d : Fin 2)
    (h : Magma.isExact (tab6D a b c d) endE6D endX06D = true) :
    ∃ i, mem6D i = tab6D a b c d :=
  ⟨_, mem_rank6D a b c d h⟩

/-- A magma on `Fin 6` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end6D`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact6D` turns that into a member index. -/
theorem exists_end6D {M : Magma (Fin 6)} (hE : ∀ j, M.IsEndo (endE6D j))
    (hX : ∀ j, ¬ M.IsEndo (endX6D j)) : ∃ i, end6D i = M := by
  have hP : ∀ i, M.IsEndo (permE6D i) := by
    intro i; rw [permE6D_eq_endE6D]; exact hE (uidx6D i)
  have hop : M.op = Magma.transport permE6D tr6D (fun i ↦ M.op (rep6D i).1 (rep6D i).2) :=
    Magma.op_eq_transport (rep := rep6D) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE6D) (idx := stabIdx6D0) (a := (rep6D 0).1) (b := (rep6D 0).2)
    (val := val6D0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE6D) (idx := stabIdx6D1) (a := (rep6D 1).1) (b := (rep6D 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE6D) (idx := stabIdx6D2) (a := (rep6D 2).1) (b := (rep6D 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE6D) (idx := stabIdx6D3) (a := (rep6D 3).1) (b := (rep6D 3).2)
    (val := val6D3) hP (by decide) (by decide)
  have hdec : dec6D a b c d = fun i ↦ M.op (rep6D i).1 (rep6D i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab6D a b c d = M.op := by
    rw [tab6D_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab6D a b c d) endE6D endX06D = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, fun j ↦ hX (x0idx6D j)⟩
  obtain ⟨i, hi⟩ := mem_of_isExact6D a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose endomorphism
monoid is exactly the order-`36` monoid of `Magma.endE6D`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end6D {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 6) (Magma.end6D i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.end6D j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end6D i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end6D
    (fun k ↦ (Magma.end6D_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end6D_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
