import equational_theories.Definability.ExactEnd4

/-!
# The exact-endomorphism class `K` on `Fin 4`

One class of `Definability/ExactEnd4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `4`: `⟨(0 1)(2 3), (0 2)(1 3)⟩`

`End(M)` is `8` maps, so `Aut(M)` -- its unit group -- is these `4` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `16`
independent cells. -/

/-- The `4` elements of the group: `()`, `(0 1)(2 3)`, `(0 2)(1 3)`, `(0 3)(1 2)`. -/
def pE4K0 : Fin 4 → Fin 4 := id
def pE4K1 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
def pE4K2 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pE4K3 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permE4K : Fin 4 → Fin 4 → Fin 4
  | 0 => pE4K0
  | 1 => pE4K1
  | 2 => pE4K2
  | 3 => pE4K3

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `256` self-maps of `Fin 4`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps4` indexes the self-maps, digit by digit. -/

/-- Indices of the `8` self-maps that must be endomorphisms: `0110`, `3210`, `1001`, `2301`, `1032`,
`2332`, `0123`, `3223` (each written as its list of values at `0, 1, ..., 3`). -/
def eidx4K : Fin 8 → Fin 256
  | 0 => 20
  | 1 => 27
  | 2 => 65
  | 3 => 78
  | 4 => 177
  | 5 => 190
  | 6 => 228
  | 7 => 235

def endE4K (j : Fin 8) : Fin 4 → Fin 4 := allMaps4 (eidx4K j)

/-- Indices of the other `248`, which must not be endomorphisms. This is a table rather than a match
because nothing the kernel evaluates ever reads it: `endX` occurs only in `native_decide` goals and
under `Magma.isExact_iff`, which is a rewrite. -/
def xarr4K : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26,
  28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
  52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76,
  77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
  101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
  120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138,
  139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157,
  158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
  178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 191, 192, 193, 194, 195, 196, 197,
  198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216,
  217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 229, 230, 231, 232, 233, 234, 236, 237,
  238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]

def xidx4K (j : Fin 248) : Fin 256 :=
  ⟨min (xarr4K.getD j.1 0) 255, by omega⟩

def endX4K (j : Fin 248) : Fin 4 → Fin 4 := allMaps4 (xidx4K j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end4K` is given. -/
def uidx4K : Fin 4 → Fin 8
  | 0 => 6
  | 1 => 4
  | 2 => 3
  | 3 => 1

theorem permE4K_eq_endE4K (i : Fin 4) : permE4K i = endE4K (uidx4K i) := by
  revert i; decide

/-- One representative per orbit of the group on the `16` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep4K : Fin 4 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr4K : Fin 4 → Fin 4 → Fin 4 × Fin 4
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
def stabIdx4K0 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4K1 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4K2 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4K3 : Fin 1 → Fin 4
  | 0 => 0

/-- The `4` orbit values named by the family's arguments. -/
def dec4K (a b c d : Fin 4) : Fin 4 → Fin 4
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab4K_eq_transport`). -/
def tab4K (a b c d : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => d
  | 1, 0 => pE4K1 b
  | 1, 1 => pE4K1 a
  | 1, 2 => pE4K1 d
  | 1, 3 => pE4K1 c
  | 2, 0 => pE4K2 c
  | 2, 1 => pE4K2 d
  | 2, 2 => pE4K2 a
  | 2, 3 => pE4K2 b
  | 3, 0 => pE4K3 d
  | 3, 1 => pE4K3 c
  | 3, 2 => pE4K3 b
  | 3, 3 => pE4K3 a

theorem tab4K_eq_transport (a b c d : Fin 4) :
    tab4K a b c d = Magma.transport permE4K tr4K (dec4K a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `6` magmas on `Fin 4` whose endomorphism monoid is exactly this one, listed under one index.
Of the `256` invariant tuples these are the ones the forbidden maps rule out; naming only them keeps
the exactness test off the hot path of a family scan. -/
def mem4K : Fin 6 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4K 1 0 0 1
  | 1 => tab4K 1 0 0 2
  | 2 => tab4K 1 0 3 1
  | 3 => tab4K 1 1 1 2
  | 4 => tab4K 1 1 2 1
  | 5 => tab4K 1 1 2 2

/-- Which of the `6` members a given invariant tuple is, so that `mem_of_isExact4K` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr4K : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 5, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr4K` is addressed. -/
def encT4K (a b c d : Fin 4) : Nat :=
  a.1 * 64 +
    b.1 * 16 +
    c.1 * 4 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank4K (a b c d : Fin 4) : Fin 6 :=
  ⟨min (rankArr4K.getD (encT4K a b c d) 0) 5, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end4K (i : Fin 6) : Magma (Fin 4) := Magma.mk (mem4K i)

theorem end4K_isEndo (i : Fin 6) (j : Fin 8) : (end4K i).IsEndo (endE4K j) := by
  revert i j; native_decide

theorem end4K_not_isEndo (i : Fin 6) (j : Fin 248) : ¬ (end4K i).IsEndo (endX4K j) := by
  revert i j; native_decide

/-- `rank4K` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem4K` for the index would be a comparison per tuple and
member. -/
theorem mem_rank4K (a b c d : Fin 4)
    (h : Magma.isExact (tab4K a b c d) endE4K endX4K = true) :
    mem4K (rank4K a b c d) = tab4K a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `6` listed
members. -/
theorem mem_of_isExact4K (a b c d : Fin 4)
    (h : Magma.isExact (tab4K a b c d) endE4K endX4K = true) :
    ∃ i, mem4K i = tab4K a b c d :=
  ⟨_, mem_rank4K a b c d h⟩

/-- A magma on `Fin 4` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end4K`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact4K` turns that into a member index. -/
theorem exists_end4K {M : Magma (Fin 4)} (hE : ∀ j, M.IsEndo (endE4K j))
    (hX : ∀ j, ¬ M.IsEndo (endX4K j)) : ∃ i, end4K i = M := by
  have hP : ∀ i, M.IsEndo (permE4K i) := by
    intro i; rw [permE4K_eq_endE4K]; exact hE (uidx4K i)
  have hop : M.op = Magma.transport permE4K tr4K (fun i ↦ M.op (rep4K i).1 (rep4K i).2) :=
    Magma.op_eq_transport (rep := rep4K) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE4K) (idx := stabIdx4K0) (a := (rep4K 0).1) (b := (rep4K 0).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE4K) (idx := stabIdx4K1) (a := (rep4K 1).1) (b := (rep4K 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE4K) (idx := stabIdx4K2) (a := (rep4K 2).1) (b := (rep4K 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE4K) (idx := stabIdx4K3) (a := (rep4K 3).1) (b := (rep4K 3).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec4K a b c d = fun i ↦ M.op (rep4K i).1 (rep4K i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab4K a b c d = M.op := by
    rw [tab4K_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab4K a b c d) endE4K endX4K = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExact4K a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose endomorphism
monoid is exactly the order-`8` monoid of `Magma.endE4K`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end4K {L L' : Law.NatMagmaLaw} {i : Fin 6}
    (hsrc : @satisfies _ (Fin 4) (Magma.end4K i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.end4K j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end4K i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end4K
    (fun k ↦ (Magma.end4K_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end4K_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
