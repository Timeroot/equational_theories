import equational_theories.Definability.ExactEnd4

/-!
# The exact-endomorphism class `J` on `Fin 4`

One class of `Definability/ExactEnd4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `4`: `⟨(0 3)(1 2), (1 2)⟩`

`End(M)` is `10` maps, so `Aut(M)` -- its unit group -- is these `4` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `6` orbit values rather than `16`
independent cells. -/

/-- The `4` elements of the group: `()`, `(1 2)`, `(0 3)`, `(0 3)(1 2)`. -/
def pE4J0 : Fin 4 → Fin 4 := id
def pE4J1 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pE4J2 : Fin 4 → Fin 4 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0
def pE4J3 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permE4J : Fin 4 → Fin 4 → Fin 4
  | 0 => pE4J0
  | 1 => pE4J1
  | 2 => pE4J2
  | 3 => pE4J3

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `256` self-maps of `Fin 4`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps4` indexes the self-maps, digit by digit. -/

/-- Indices of the `10` self-maps that must be endomorphisms: `0000`, `3210`, `3120`, `1111`,
`1221`, `2112`, `2222`, `0213`, `0123`, `3333` (each written as its list of values at `0, 1, ...,
3`). -/
def eidx4J : Fin 10 → Fin 256
  | 0 => 0
  | 1 => 27
  | 2 => 39
  | 3 => 85
  | 4 => 105
  | 5 => 150
  | 6 => 170
  | 7 => 216
  | 8 => 228
  | 9 => 255

def endE4J (j : Fin 10) : Fin 4 → Fin 4 := allMaps4 (eidx4J j)

/-- Indices of the other `246`, which must not be endomorphisms. This is a table rather than a match
because nothing the kernel evaluates ever reads it: `endX` occurs only in `native_decide` goals and
under `Magma.isExact_iff`, which is a rewrite. -/
def xarr4J : Array Nat := #[
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
  53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76,
  77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
  101, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
  121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
  140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 151, 152, 153, 154, 155, 156, 157, 158, 159,
  160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179,
  180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198,
  199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 217, 218,
  219, 220, 221, 222, 223, 224, 225, 226, 227, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238,
  239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]

def xidx4J (j : Fin 246) : Fin 256 :=
  ⟨min (xarr4J.getD j.1 0) 255, by omega⟩

def endX4J (j : Fin 246) : Fin 4 → Fin 4 := allMaps4 (xidx4J j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end4J` is given. -/
def uidx4J : Fin 4 → Fin 10
  | 0 => 8
  | 1 => 7
  | 2 => 2
  | 3 => 1

theorem permE4J_eq_endE4J (i : Fin 4) : permE4J i = endE4J (uidx4J i) := by
  revert i; decide

/-- One representative per orbit of the group on the `16` cells; there are `6`, so an invariant
operation is `6` values. -/
def rep4J : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr4J : Fin 4 → Fin 4 → Fin 6 × Fin 4
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (2, 0)
  | 1, 0 => (3, 0)
  | 1, 1 => (4, 0)
  | 1, 2 => (5, 0)
  | 1, 3 => (3, 2)
  | 2, 0 => (3, 1)
  | 2, 1 => (5, 1)
  | 2, 2 => (4, 1)
  | 2, 3 => (3, 3)
  | 3, 0 => (2, 2)
  | 3, 1 => (1, 2)
  | 3, 2 => (1, 3)
  | 3, 3 => (0, 2)

/-- The `2` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4J0 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1
def val4J0 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4J1 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4J2 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1
def val4J2 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4J3 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4J4 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 2
def val4J4 : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4J5 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 2
def val4J5 : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- The `6` orbit values named by the family's arguments. -/
def dec4J (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 6 → Fin 4
  | 0 => val4J0 a
  | 1 => b
  | 2 => val4J2 c
  | 3 => d
  | 4 => val4J4 e
  | 5 => val4J5 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab4J_eq_transport`). -/
def tab4J (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => val4J0 a
  | 0, 1 => b
  | 0, 2 => pE4J1 b
  | 0, 3 => val4J2 c
  | 1, 0 => d
  | 1, 1 => val4J4 e
  | 1, 2 => val4J5 f
  | 1, 3 => pE4J2 d
  | 2, 0 => pE4J1 d
  | 2, 1 => pE4J1 (val4J5 f)
  | 2, 2 => pE4J1 (val4J4 e)
  | 2, 3 => pE4J3 d
  | 3, 0 => pE4J2 (val4J2 c)
  | 3, 1 => pE4J2 b
  | 3, 2 => pE4J3 b
  | 3, 3 => pE4J2 (val4J0 a)

theorem tab4J_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) :
    tab4J a b c d e f = Magma.transport permE4J tr4J (dec4J a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 4` whose endomorphism monoid is exactly this one, listed under one index.
Of the `256` invariant tuples these are the ones the forbidden maps rule out; naming only them keeps
the exactness test off the hot path of a family scan. -/
def mem4J : Fin 2 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4J 0 2 0 3 0 1
  | 1 => tab4J 0 3 1 2 0 0

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact4J` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr4J : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr4J` is addressed. -/
def encT4J (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Nat :=
  a.1 * 128 +
    b.1 * 32 +
    c.1 * 16 +
    d.1 * 4 +
    e.1 * 2 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank4J (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 2 :=
  ⟨min (rankArr4J.getD (encT4J a b c d e f) 0) 1, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end4J (i : Fin 2) : Magma (Fin 4) := Magma.mk (mem4J i)

theorem end4J_isEndo (i : Fin 2) (j : Fin 10) : (end4J i).IsEndo (endE4J j) := by
  revert i j; native_decide

theorem end4J_not_isEndo (i : Fin 2) (j : Fin 246) : ¬ (end4J i).IsEndo (endX4J j) := by
  revert i j; native_decide

/-- `rank4J` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem4J` for the index would be a comparison per tuple and
member. -/
theorem mem_rank4J (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2)
    (h : Magma.isExact (tab4J a b c d e f) endE4J endX4J = true) :
    mem4J (rank4J a b c d e f) = tab4J a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact4J (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2)
    (h : Magma.isExact (tab4J a b c d e f) endE4J endX4J = true) :
    ∃ i, mem4J i = tab4J a b c d e f :=
  ⟨_, mem_rank4J a b c d e f h⟩

/-- A magma on `Fin 4` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end4J`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact4J` turns that into a member index. -/
theorem exists_end4J {M : Magma (Fin 4)} (hE : ∀ j, M.IsEndo (endE4J j))
    (hX : ∀ j, ¬ M.IsEndo (endX4J j)) : ∃ i, end4J i = M := by
  have hP : ∀ i, M.IsEndo (permE4J i) := by
    intro i; rw [permE4J_eq_endE4J]; exact hE (uidx4J i)
  have hop : M.op = Magma.transport permE4J tr4J (fun i ↦ M.op (rep4J i).1 (rep4J i).2) :=
    Magma.op_eq_transport (rep := rep4J) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE4J) (idx := stabIdx4J0) (a := (rep4J 0).1) (b := (rep4J 0).2)
    (val := val4J0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE4J) (idx := stabIdx4J1) (a := (rep4J 1).1) (b := (rep4J 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE4J) (idx := stabIdx4J2) (a := (rep4J 2).1) (b := (rep4J 2).2)
    (val := val4J2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE4J) (idx := stabIdx4J3) (a := (rep4J 3).1) (b := (rep4J 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE4J) (idx := stabIdx4J4) (a := (rep4J 4).1) (b := (rep4J 4).2)
    (val := val4J4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE4J) (idx := stabIdx4J5) (a := (rep4J 5).1) (b := (rep4J 5).2)
    (val := val4J5) hP (by decide) (by decide)
  have hdec : dec4J a b c d e f = fun i ↦ M.op (rep4J i).1 (rep4J i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tab4J a b c d e f = M.op := by
    rw [tab4J_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab4J a b c d e f) endE4J endX4J = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExact4J a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose endomorphism
monoid is exactly the order-`10` monoid of `Magma.endE4J`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end4J {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 4) (Magma.end4J i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.end4J j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end4J i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end4J
    (fun k ↦ (Magma.end4J_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end4J_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
