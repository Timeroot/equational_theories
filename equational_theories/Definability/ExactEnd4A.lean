import equational_theories.Definability.ExactEnd4

/-!
# The exact-endomorphism class `A` on `Fin 4`

One class of `Definability/ExactEnd4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `4`: `⟨(0 1)(2 3), (0 2)(1 3)⟩`

`End(M)` is `16` maps, so `Aut(M)` -- its unit group -- is these `4` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `16`
independent cells. -/

/-- The `4` elements of the group: `()`, `(0 1)(2 3)`, `(0 2)(1 3)`, `(0 3)(1 2)`. -/
def pE4A0 : Fin 4 → Fin 4 := id
def pE4A1 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
def pE4A2 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pE4A3 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permE4A : Fin 4 → Fin 4 → Fin 4
  | 0 => pE4A0
  | 1 => pE4A1
  | 2 => pE4A2
  | 3 => pE4A3

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `256` self-maps of `Fin 4`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps4` indexes the self-maps, digit by digit. -/

/-- Indices of the `16` self-maps that must be endomorphisms: `1010`, `0110`, `3210`, `2310`,
`1001`, `0101`, `3201`, `2301`, `1032`, `0132`, `3232`, `2332`, ... (each written as its list of
values at `0, 1, ..., 3`). -/
def eidx4A : Fin 16 → Fin 256
  | 0 => 17
  | 1 => 20
  | 2 => 27
  | 3 => 30
  | 4 => 65
  | 5 => 68
  | 6 => 75
  | 7 => 78
  | 8 => 177
  | 9 => 180
  | 10 => 187
  | 11 => 190
  | 12 => 225
  | 13 => 228
  | 14 => 235
  | _ => 238

def endE4A (j : Fin 16) : Fin 4 → Fin 4 := allMaps4 (eidx4A j)

/-- Indices of the other `240`, which must not be endomorphisms. This is a table rather than a match
because nothing the kernel evaluates ever reads it: `endX` occurs only in `native_decide` goals and
under `Magma.isExact_iff`, which is a rewrite. -/
def xarr4A : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 21, 22, 23, 24, 25, 26, 28,
  29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
  54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66, 67, 69, 70, 71, 72, 73, 74, 76, 77, 79, 80, 81,
  82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
  104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
  123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141,
  142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
  161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 178, 179, 181,
  182, 183, 184, 185, 186, 188, 189, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
  203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221,
  222, 223, 224, 226, 227, 229, 230, 231, 232, 233, 234, 236, 237, 239, 240, 241, 242, 243, 244,
  245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]

def xidx4A (j : Fin 240) : Fin 256 :=
  ⟨min (xarr4A.getD j.1 0) 255, by omega⟩

def endX4A (j : Fin 240) : Fin 4 → Fin 4 := allMaps4 (xidx4A j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end4A` is given. -/
def uidx4A : Fin 4 → Fin 16
  | 0 => 13
  | 1 => 8
  | 2 => 7
  | 3 => 2

theorem permE4A_eq_endE4A (i : Fin 4) : permE4A i = endE4A (uidx4A i) := by
  revert i; decide

/-- One representative per orbit of the group on the `16` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep4A : Fin 4 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr4A : Fin 4 → Fin 4 → Fin 4 × Fin 4
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 1, 0 => (1, 1)
  | 1, 1 => (0, 1)
  | 1, 2 => (3, 1)
  | 1, 3 => (2, 1)
  | 2, 0 => (2, 2)
  | 2, 1 => (3, 2)
  | 2, 2 => (0, 2)
  | 2, 3 => (1, 2)
  | 3, 0 => (3, 3)
  | 3, 1 => (2, 3)
  | 3, 2 => (1, 3)
  | 3, 3 => (0, 3)

/-- The one group element fixing both coordinates of orbit `0`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4A0 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4A1 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4A2 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4A3 : Fin 1 → Fin 4
  | 0 => 0

/-- The `4` orbit values named by the family's arguments. -/
def dec4A (a b c d : Fin 4) : Fin 4 → Fin 4
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab4A_eq_transport`). -/
def tab4A (a b c d : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => d
  | 1, 0 => pE4A1 b
  | 1, 1 => pE4A1 a
  | 1, 2 => pE4A1 d
  | 1, 3 => pE4A1 c
  | 2, 0 => pE4A2 c
  | 2, 1 => pE4A2 d
  | 2, 2 => pE4A2 a
  | 2, 3 => pE4A2 b
  | 3, 0 => pE4A3 d
  | 3, 1 => pE4A3 c
  | 3, 2 => pE4A3 b
  | 3, 3 => pE4A3 a

theorem tab4A_eq_transport (a b c d : Fin 4) :
    tab4A a b c d = Magma.transport permE4A tr4A (dec4A a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `2` magmas on `Fin 4` whose endomorphism monoid is exactly this one, listed under one index.
Of the `256` invariant tuples these are the ones the forbidden maps rule out; naming only them keeps
the exactness test off the hot path of a family scan. -/
def mem4A : Fin 2 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4A 1 0 3 2
  | 1 => tab4A 1 1 1 1

/-- Which of the `2` members a given invariant tuple is, so that `mem_of_isExact4A` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr4A : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr4A` is addressed. -/
def encT4A (a b c d : Fin 4) : Nat :=
  a.1 * 64 +
    b.1 * 16 +
    c.1 * 4 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank4A (a b c d : Fin 4) : Fin 2 :=
  ⟨min (rankArr4A.getD (encT4A a b c d) 0) 1, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end4A (i : Fin 2) : Magma (Fin 4) := Magma.mk (mem4A i)

theorem end4A_isEndo (i : Fin 2) (j : Fin 16) : (end4A i).IsEndo (endE4A j) := by
  revert i j; native_decide

theorem end4A_not_isEndo (i : Fin 2) (j : Fin 240) : ¬ (end4A i).IsEndo (endX4A j) := by
  revert i j; native_decide

/-- `rank4A` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem4A` for the index would be a comparison per tuple and
member. -/
theorem mem_rank4A (a b c d : Fin 4)
    (h : Magma.isExact (tab4A a b c d) endE4A endX4A = true) :
    mem4A (rank4A a b c d) = tab4A a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `2` listed
members. -/
theorem mem_of_isExact4A (a b c d : Fin 4)
    (h : Magma.isExact (tab4A a b c d) endE4A endX4A = true) :
    ∃ i, mem4A i = tab4A a b c d :=
  ⟨_, mem_rank4A a b c d h⟩

/-- A magma on `Fin 4` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end4A`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact4A` turns that into a member index. -/
theorem exists_end4A {M : Magma (Fin 4)} (hE : ∀ j, M.IsEndo (endE4A j))
    (hX : ∀ j, ¬ M.IsEndo (endX4A j)) : ∃ i, end4A i = M := by
  have hP : ∀ i, M.IsEndo (permE4A i) := by
    intro i; rw [permE4A_eq_endE4A]; exact hE (uidx4A i)
  have hop : M.op = Magma.transport permE4A tr4A (fun i ↦ M.op (rep4A i).1 (rep4A i).2) :=
    Magma.op_eq_transport (rep := rep4A) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE4A) (idx := stabIdx4A0) (a := (rep4A 0).1) (b := (rep4A 0).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE4A) (idx := stabIdx4A1) (a := (rep4A 1).1) (b := (rep4A 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE4A) (idx := stabIdx4A2) (a := (rep4A 2).1) (b := (rep4A 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE4A) (idx := stabIdx4A3) (a := (rep4A 3).1) (b := (rep4A 3).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec4A a b c d = fun i ↦ M.op (rep4A i).1 (rep4A i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab4A a b c d = M.op := by
    rw [tab4A_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab4A a b c d) endE4A endX4A = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExact4A a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose endomorphism
monoid is exactly the order-`16` monoid of `Magma.endE4A`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end4A {L L' : Law.NatMagmaLaw} {i : Fin 2}
    (hsrc : @satisfies _ (Fin 4) (Magma.end4A i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.end4A j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end4A i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end4A
    (fun k ↦ (Magma.end4A_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end4A_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
