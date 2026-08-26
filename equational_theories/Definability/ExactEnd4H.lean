import equational_theories.Definability.ExactEnd4

/-!
# The exact-endomorphism class `H` on `Fin 4`

One class of `Definability/ExactEnd4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `4`: `⟨(0 3)(1 2), (1 2)⟩`

`End(M)` is `4` maps, so `Aut(M)` -- its unit group -- is these `4` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `6` orbit values rather than `16`
independent cells. -/

/-- The `4` elements of the group: `()`, `(1 2)`, `(0 3)`, `(0 3)(1 2)`. -/
def pE4H0 : Fin 4 → Fin 4 := id
def pE4H1 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pE4H2 : Fin 4 → Fin 4 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0
def pE4H3 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permE4H : Fin 4 → Fin 4 → Fin 4
  | 0 => pE4H0
  | 1 => pE4H1
  | 2 => pE4H2
  | 3 => pE4H3

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `256` self-maps of `Fin 4`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps4` indexes the self-maps, digit by digit. -/

/-- Indices of the `4` self-maps that must be endomorphisms: `3210`, `3120`, `0213`, `0123` (each
written as its list of values at `0, 1, ..., 3`). -/
def eidx4H : Fin 4 → Fin 256
  | 0 => 27
  | 1 => 39
  | 2 => 216
  | 3 => 228

def endE4H (j : Fin 4) : Fin 4 → Fin 4 := allMaps4 (eidx4H j)

/-- Indices of the other `252`, which must not be endomorphisms. This is a table rather than a match
because nothing the kernel evaluates ever reads it: `endX` occurs only in `native_decide` goals and
under `Magma.isExact_iff`, which is a rewrite. -/
def xarr4H : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
  52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
  76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
  119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
  138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156,
  157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
  176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194,
  195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213,
  214, 215, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 229, 230, 231, 232, 233, 234,
  235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
  254, 255]

def xidx4H (j : Fin 252) : Fin 256 :=
  ⟨min (xarr4H.getD j.1 0) 255, by omega⟩

def endX4H (j : Fin 252) : Fin 4 → Fin 4 := allMaps4 (xidx4H j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end4H` is given. -/
def uidx4H : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

theorem permE4H_eq_endE4H (i : Fin 4) : permE4H i = endE4H (uidx4H i) := by
  revert i; decide

/-- One representative per orbit of the group on the `16` cells; there are `6`, so an invariant
operation is `6` values. -/
def rep4H : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (1, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr4H : Fin 4 → Fin 4 → Fin 6 × Fin 4
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
def stabIdx4H0 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1
def val4H0 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4H1 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4H2 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1
def val4H2 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4H3 : Fin 1 → Fin 4
  | 0 => 0

/-- The `2` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4H4 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 2
def val4H4 : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- The `2` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be one of `1`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdx4H5 : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 2
def val4H5 : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- The `6` orbit values named by the family's arguments. -/
def dec4H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 6 → Fin 4
  | 0 => val4H0 a
  | 1 => b
  | 2 => val4H2 c
  | 3 => d
  | 4 => val4H4 e
  | 5 => val4H5 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab4H_eq_transport`). -/
def tab4H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => val4H0 a
  | 0, 1 => b
  | 0, 2 => pE4H1 b
  | 0, 3 => val4H2 c
  | 1, 0 => d
  | 1, 1 => val4H4 e
  | 1, 2 => val4H5 f
  | 1, 3 => pE4H2 d
  | 2, 0 => pE4H1 d
  | 2, 1 => pE4H1 (val4H5 f)
  | 2, 2 => pE4H1 (val4H4 e)
  | 2, 3 => pE4H3 d
  | 3, 0 => pE4H2 (val4H2 c)
  | 3, 1 => pE4H2 b
  | 3, 2 => pE4H3 b
  | 3, 3 => pE4H2 (val4H0 a)

theorem tab4H_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) :
    tab4H a b c d e f = Magma.transport permE4H tr4H (dec4H a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `56` magmas on `Fin 4` whose endomorphism monoid is exactly this one, listed under one
index. Of the `256` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def memRow4H0 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 0 0 0 1 0
  | 1 => tab4H 1 0 0 0 1 1
  | 2 => tab4H 1 0 0 1 1 1
  | 3 => tab4H 1 0 0 2 1 0
  | 4 => tab4H 1 0 0 2 1 1
  | 5 => tab4H 1 0 0 3 1 0
  | 6 => tab4H 1 0 0 3 1 1
  | _ => tab4H 1 0 1 0 1 0
def memRow4H1 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 0 1 0 1 1
  | 1 => tab4H 1 0 1 1 1 0
  | 2 => tab4H 1 0 1 2 1 0
  | 3 => tab4H 1 0 1 2 1 1
  | 4 => tab4H 1 0 1 3 1 0
  | 5 => tab4H 1 0 1 3 1 1
  | 6 => tab4H 1 1 0 0 1 1
  | _ => tab4H 1 1 0 1 1 0
def memRow4H2 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 1 0 1 1 1
  | 1 => tab4H 1 1 0 2 1 0
  | 2 => tab4H 1 1 0 2 1 1
  | 3 => tab4H 1 1 0 3 1 0
  | 4 => tab4H 1 1 0 3 1 1
  | 5 => tab4H 1 1 1 0 1 0
  | 6 => tab4H 1 1 1 1 1 0
  | _ => tab4H 1 1 1 1 1 1
def memRow4H3 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 1 1 2 1 0
  | 1 => tab4H 1 1 1 2 1 1
  | 2 => tab4H 1 1 1 3 1 0
  | 3 => tab4H 1 1 1 3 1 1
  | 4 => tab4H 1 2 0 0 1 0
  | 5 => tab4H 1 2 0 0 1 1
  | 6 => tab4H 1 2 0 1 1 0
  | _ => tab4H 1 2 0 1 1 1
def memRow4H4 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 2 0 2 1 0
  | 1 => tab4H 1 2 0 2 1 1
  | 2 => tab4H 1 2 0 3 1 1
  | 3 => tab4H 1 2 1 0 1 0
  | 4 => tab4H 1 2 1 0 1 1
  | 5 => tab4H 1 2 1 1 1 0
  | 6 => tab4H 1 2 1 1 1 1
  | _ => tab4H 1 2 1 2 1 0
def memRow4H5 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 2 1 2 1 1
  | 1 => tab4H 1 2 1 3 1 0
  | 2 => tab4H 1 3 0 0 1 0
  | 3 => tab4H 1 3 0 0 1 1
  | 4 => tab4H 1 3 0 1 1 0
  | 5 => tab4H 1 3 0 1 1 1
  | 6 => tab4H 1 3 0 2 1 1
  | _ => tab4H 1 3 0 3 1 0
def memRow4H6 : Fin 8 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4H 1 3 0 3 1 1
  | 1 => tab4H 1 3 1 0 1 0
  | 2 => tab4H 1 3 1 0 1 1
  | 3 => tab4H 1 3 1 1 1 0
  | 4 => tab4H 1 3 1 1 1 1
  | 5 => tab4H 1 3 1 2 1 0
  | 6 => tab4H 1 3 1 3 1 0
  | _ => tab4H 1 3 1 3 1 1
def mem4H (i : Fin 56) : Fin 4 → Fin 4 → Fin 4 :=
  match (i.1 / 8 : Nat) with
  | 0 => memRow4H0 ⟨i.1 % 8, by omega⟩
  | 1 => memRow4H1 ⟨i.1 % 8, by omega⟩
  | 2 => memRow4H2 ⟨i.1 % 8, by omega⟩
  | 3 => memRow4H3 ⟨i.1 % 8, by omega⟩
  | 4 => memRow4H4 ⟨i.1 % 8, by omega⟩
  | 5 => memRow4H5 ⟨i.1 % 8, by omega⟩
  | _ => memRow4H6 ⟨i.1 % 8, by omega⟩

/-- Which of the `56` members a given invariant tuple is, so that `mem_of_isExact4H` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr4H : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 3, 4, 0, 0, 5, 6, 0, 0, 7, 8, 0, 0, 9, 0, 0, 0, 10, 11, 0, 0, 12,
  13, 0, 0, 0, 14, 0, 0, 15, 16, 0, 0, 17, 18, 0, 0, 19, 20, 0, 0, 21, 0, 0, 0, 22, 23, 0, 0, 24,
  25, 0, 0, 26, 27, 0, 0, 28, 29, 0, 0, 30, 31, 0, 0, 32, 33, 0, 0, 0, 34, 0, 0, 35, 36, 0, 0,
  37, 38, 0, 0, 39, 40, 0, 0, 41, 0, 0, 0, 42, 43, 0, 0, 44, 45, 0, 0, 0, 46, 0, 0, 47, 48, 0, 0,
  49, 50, 0, 0, 51, 52, 0, 0, 53, 0, 0, 0, 54, 55]

/-- The arguments as one mixed-radix index, which is how `rankArr4H` is addressed. -/
def encT4H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Nat :=
  a.1 * 128 +
    b.1 * 32 +
    c.1 * 16 +
    d.1 * 4 +
    e.1 * 2 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank4H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2) : Fin 56 :=
  ⟨min (rankArr4H.getD (encT4H a b c d e f) 0) 55, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end4H (i : Fin 56) : Magma (Fin 4) := Magma.mk (mem4H i)

theorem end4H_isEndo (i : Fin 56) (j : Fin 4) : (end4H i).IsEndo (endE4H j) := by
  revert i j; native_decide

theorem end4H_not_isEndo (i : Fin 56) (j : Fin 252) : ¬ (end4H i).IsEndo (endX4H j) := by
  revert i j; native_decide

/-- `rank4H` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem4H` for the index would be a comparison per tuple and
member. -/
theorem mem_rank4H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2)
    (h : Magma.isExact (tab4H a b c d e f) endE4H endX4H = true) :
    mem4H (rank4H a b c d e f) = tab4H a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `56` listed
members. -/
theorem mem_of_isExact4H (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 4) (e f : Fin 2)
    (h : Magma.isExact (tab4H a b c d e f) endE4H endX4H = true) :
    ∃ i, mem4H i = tab4H a b c d e f :=
  ⟨_, mem_rank4H a b c d e f h⟩

/-- A magma on `Fin 4` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end4H`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact4H` turns that into a member index. -/
theorem exists_end4H {M : Magma (Fin 4)} (hE : ∀ j, M.IsEndo (endE4H j))
    (hX : ∀ j, ¬ M.IsEndo (endX4H j)) : ∃ i, end4H i = M := by
  have hP : ∀ i, M.IsEndo (permE4H i) := by
    intro i; rw [permE4H_eq_endE4H]; exact hE (uidx4H i)
  have hop : M.op = Magma.transport permE4H tr4H (fun i ↦ M.op (rep4H i).1 (rep4H i).2) :=
    Magma.op_eq_transport (rep := rep4H) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE4H) (idx := stabIdx4H0) (a := (rep4H 0).1) (b := (rep4H 0).2)
    (val := val4H0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE4H) (idx := stabIdx4H1) (a := (rep4H 1).1) (b := (rep4H 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE4H) (idx := stabIdx4H2) (a := (rep4H 2).1) (b := (rep4H 2).2)
    (val := val4H2) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE4H) (idx := stabIdx4H3) (a := (rep4H 3).1) (b := (rep4H 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE4H) (idx := stabIdx4H4) (a := (rep4H 4).1) (b := (rep4H 4).2)
    (val := val4H4) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE4H) (idx := stabIdx4H5) (a := (rep4H 5).1) (b := (rep4H 5).2)
    (val := val4H5) hP (by decide) (by decide)
  have hdec : dec4H a b c d e f = fun i ↦ M.op (rep4H i).1 (rep4H i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tab4H a b c d e f = M.op := by
    rw [tab4H_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab4H a b c d e f) endE4H endX4H = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExact4H a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose endomorphism
monoid is exactly the order-`4` monoid of `Magma.endE4H`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end4H {L L' : Law.NatMagmaLaw} {i : Fin 56}
    (hsrc : @satisfies _ (Fin 4) (Magma.end4H i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.end4H j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end4H i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end4H
    (fun k ↦ (Magma.end4H_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end4H_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
