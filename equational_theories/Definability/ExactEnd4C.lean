import equational_theories.Definability.ExactEnd4

/-!
# The exact-endomorphism class `C` on `Fin 4`

One class of `Definability/ExactEnd4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `4`: `⟨(0 1)(2 3), (0 2)(1 3)⟩`

`End(M)` is `4` maps, so `Aut(M)` -- its unit group -- is these `4` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `4` orbit values rather than `16`
independent cells. -/

/-- The `4` elements of the group: `()`, `(0 1)(2 3)`, `(0 2)(1 3)`, `(0 3)(1 2)`. -/
def pE4C0 : Fin 4 → Fin 4 := id
def pE4C1 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
def pE4C2 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pE4C3 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permE4C : Fin 4 → Fin 4 → Fin 4
  | 0 => pE4C0
  | 1 => pE4C1
  | 2 => pE4C2
  | 3 => pE4C3

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `256` self-maps of `Fin 4`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps4` indexes the self-maps, digit by digit. -/

/-- Indices of the `4` self-maps that must be endomorphisms: `3210`, `2301`, `1032`, `0123` (each
written as its list of values at `0, 1, ..., 3`). -/
def eidx4C : Fin 4 → Fin 256
  | 0 => 27
  | 1 => 78
  | 2 => 177
  | 3 => 228

def endE4C (j : Fin 4) : Fin 4 → Fin 4 := allMaps4 (eidx4C j)

/-- Indices of the other `252`, which must not be endomorphisms. This is a table rather than a match
because nothing the kernel evaluates ever reads it: `endX` occurs only in `native_decide` goals and
under `Magma.isExact_iff`, which is a rewrite. -/
def xarr4C : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
  51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
  119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
  138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156,
  157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
  176, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195,
  196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214,
  215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 229, 230, 231, 232, 233, 234,
  235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
  254, 255]

def xidx4C (j : Fin 252) : Fin 256 :=
  ⟨min (xarr4C.getD j.1 0) 255, by omega⟩

def endX4C (j : Fin 252) : Fin 4 → Fin 4 := allMaps4 (xidx4C j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end4C` is given. -/
def uidx4C : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

theorem permE4C_eq_endE4C (i : Fin 4) : permE4C i = endE4C (uidx4C i) := by
  revert i; decide

/-- One representative per orbit of the group on the `16` cells; there are `4`, so an invariant
operation is `4` values. -/
def rep4C : Fin 4 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr4C : Fin 4 → Fin 4 → Fin 4 × Fin 4
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
def stabIdx4C0 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4C1 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4C2 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4C3 : Fin 1 → Fin 4
  | 0 => 0

/-- The `4` orbit values named by the family's arguments. -/
def dec4C (a b c d : Fin 4) : Fin 4 → Fin 4
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab4C_eq_transport`). -/
def tab4C (a b c d : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => d
  | 1, 0 => pE4C1 b
  | 1, 1 => pE4C1 a
  | 1, 2 => pE4C1 d
  | 1, 3 => pE4C1 c
  | 2, 0 => pE4C2 c
  | 2, 1 => pE4C2 d
  | 2, 2 => pE4C2 a
  | 2, 3 => pE4C2 b
  | 3, 0 => pE4C3 d
  | 3, 1 => pE4C3 c
  | 3, 2 => pE4C3 b
  | 3, 3 => pE4C3 a

theorem tab4C_eq_transport (a b c d : Fin 4) :
    tab4C a b c d = Magma.transport permE4C tr4C (dec4C a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `132` magmas on `Fin 4` whose endomorphism monoid is exactly this one, listed under one
index. Of the `256` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def memRow4C0 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 1 0 0 3
  | 1 => tab4C 1 0 1 3
  | 2 => tab4C 1 0 2 0
  | 3 => tab4C 1 0 2 1
  | 4 => tab4C 1 0 2 2
  | 5 => tab4C 1 0 3 3
  | 6 => tab4C 1 1 0 1
  | 7 => tab4C 1 1 0 2
  | 8 => tab4C 1 1 0 3
  | 9 => tab4C 1 1 1 0
  | 10 => tab4C 1 1 2 0
  | _ => tab4C 1 1 3 0
def memRow4C1 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 1 2 0 0
  | 1 => tab4C 1 2 0 1
  | 2 => tab4C 1 2 0 2
  | 3 => tab4C 1 2 0 3
  | 4 => tab4C 1 2 1 0
  | 5 => tab4C 1 2 1 1
  | 6 => tab4C 1 2 1 2
  | 7 => tab4C 1 2 1 3
  | 8 => tab4C 1 2 2 0
  | 9 => tab4C 1 2 2 1
  | 10 => tab4C 1 2 2 2
  | _ => tab4C 1 2 2 3
def memRow4C2 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 1 2 3 0
  | 1 => tab4C 1 2 3 1
  | 2 => tab4C 1 2 3 2
  | 3 => tab4C 1 2 3 3
  | 4 => tab4C 1 3 0 0
  | 5 => tab4C 1 3 0 1
  | 6 => tab4C 1 3 0 2
  | 7 => tab4C 1 3 0 3
  | 8 => tab4C 1 3 1 0
  | 9 => tab4C 1 3 1 1
  | 10 => tab4C 1 3 1 2
  | _ => tab4C 1 3 1 3
def memRow4C3 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 1 3 2 0
  | 1 => tab4C 1 3 2 1
  | 2 => tab4C 1 3 2 2
  | 3 => tab4C 1 3 2 3
  | 4 => tab4C 1 3 3 0
  | 5 => tab4C 1 3 3 1
  | 6 => tab4C 1 3 3 2
  | 7 => tab4C 1 3 3 3
  | 8 => tab4C 2 0 0 3
  | 9 => tab4C 2 0 1 0
  | 10 => tab4C 2 0 1 1
  | _ => tab4C 2 0 1 2
def memRow4C4 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 2 0 1 3
  | 1 => tab4C 2 0 2 1
  | 2 => tab4C 2 0 2 2
  | 3 => tab4C 2 0 2 3
  | 4 => tab4C 2 0 3 0
  | 5 => tab4C 2 0 3 1
  | 6 => tab4C 2 0 3 2
  | 7 => tab4C 2 0 3 3
  | 8 => tab4C 2 1 0 0
  | 9 => tab4C 2 1 0 1
  | 10 => tab4C 2 1 0 2
  | _ => tab4C 2 1 1 0
def memRow4C5 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 2 1 1 1
  | 1 => tab4C 2 1 1 2
  | 2 => tab4C 2 1 1 3
  | 3 => tab4C 2 1 2 0
  | 4 => tab4C 2 1 3 0
  | 5 => tab4C 2 1 3 1
  | 6 => tab4C 2 1 3 2
  | 7 => tab4C 2 1 3 3
  | 8 => tab4C 2 2 0 3
  | 9 => tab4C 2 2 1 0
  | 10 => tab4C 2 2 1 1
  | _ => tab4C 2 2 1 2
def memRow4C6 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 2 2 1 3
  | 1 => tab4C 2 2 2 0
  | 2 => tab4C 2 2 3 0
  | 3 => tab4C 2 2 3 1
  | 4 => tab4C 2 2 3 2
  | 5 => tab4C 2 2 3 3
  | 6 => tab4C 2 3 0 3
  | 7 => tab4C 2 3 1 0
  | 8 => tab4C 2 3 1 1
  | 9 => tab4C 2 3 1 2
  | 10 => tab4C 2 3 1 3
  | _ => tab4C 2 3 2 0
def memRow4C7 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 2 3 3 0
  | 1 => tab4C 2 3 3 1
  | 2 => tab4C 2 3 3 2
  | 3 => tab4C 2 3 3 3
  | 4 => tab4C 3 0 0 1
  | 5 => tab4C 3 0 0 2
  | 6 => tab4C 3 0 1 1
  | 7 => tab4C 3 0 1 2
  | 8 => tab4C 3 0 1 3
  | 9 => tab4C 3 0 2 0
  | 10 => tab4C 3 0 2 1
  | _ => tab4C 3 0 2 2
def memRow4C8 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 3 0 2 3
  | 1 => tab4C 3 0 3 1
  | 2 => tab4C 3 0 3 2
  | 3 => tab4C 3 0 3 3
  | 4 => tab4C 3 1 0 0
  | 5 => tab4C 3 1 0 1
  | 6 => tab4C 3 1 0 2
  | 7 => tab4C 3 1 0 3
  | 8 => tab4C 3 1 1 0
  | 9 => tab4C 3 1 1 1
  | 10 => tab4C 3 1 1 2
  | _ => tab4C 3 1 2 1
def memRow4C9 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 3 1 2 2
  | 1 => tab4C 3 1 3 0
  | 2 => tab4C 3 1 3 1
  | 3 => tab4C 3 1 3 2
  | 4 => tab4C 3 2 0 1
  | 5 => tab4C 3 2 0 2
  | 6 => tab4C 3 2 0 3
  | 7 => tab4C 3 2 1 1
  | 8 => tab4C 3 2 1 2
  | 9 => tab4C 3 2 2 0
  | 10 => tab4C 3 2 2 1
  | _ => tab4C 3 2 2 2
def memRow4C10 : Fin 12 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4C 3 2 3 1
  | 1 => tab4C 3 2 3 2
  | 2 => tab4C 3 3 0 1
  | 3 => tab4C 3 3 0 2
  | 4 => tab4C 3 3 0 3
  | 5 => tab4C 3 3 1 1
  | 6 => tab4C 3 3 1 2
  | 7 => tab4C 3 3 2 0
  | 8 => tab4C 3 3 2 1
  | 9 => tab4C 3 3 2 2
  | 10 => tab4C 3 3 3 1
  | _ => tab4C 3 3 3 2
def mem4C (i : Fin 132) : Fin 4 → Fin 4 → Fin 4 :=
  match (i.1 / 12 : Nat) with
  | 0 => memRow4C0 ⟨i.1 % 12, by omega⟩
  | 1 => memRow4C1 ⟨i.1 % 12, by omega⟩
  | 2 => memRow4C2 ⟨i.1 % 12, by omega⟩
  | 3 => memRow4C3 ⟨i.1 % 12, by omega⟩
  | 4 => memRow4C4 ⟨i.1 % 12, by omega⟩
  | 5 => memRow4C5 ⟨i.1 % 12, by omega⟩
  | 6 => memRow4C6 ⟨i.1 % 12, by omega⟩
  | 7 => memRow4C7 ⟨i.1 % 12, by omega⟩
  | 8 => memRow4C8 ⟨i.1 % 12, by omega⟩
  | 9 => memRow4C9 ⟨i.1 % 12, by omega⟩
  | _ => memRow4C10 ⟨i.1 % 12, by omega⟩

/-- Which of the `132` members a given invariant tuple is, so that `mem_of_isExact4C` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr4C : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 5, 0, 6, 7, 8, 9, 0, 0, 0, 10, 0, 0, 0, 11, 0, 0,
  0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42, 43, 0, 0, 0, 44, 45, 46, 47, 48, 0, 49, 50, 51, 52, 53, 54, 55,
  56, 57, 58, 0, 59, 60, 61, 62, 63, 0, 0, 0, 64, 65, 66, 67, 0, 0, 0, 68, 69, 70, 71, 72, 73, 0,
  0, 0, 74, 75, 76, 77, 0, 0, 0, 78, 79, 80, 81, 82, 83, 0, 0, 0, 84, 85, 86, 87, 0, 88, 89, 0,
  0, 90, 91, 92, 93, 94, 95, 96, 0, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 0, 0, 107,
  108, 0, 109, 110, 111, 0, 0, 112, 113, 114, 0, 115, 116, 0, 117, 118, 119, 0, 0, 120, 121, 0,
  0, 122, 123, 124, 0, 125, 126, 0, 127, 128, 129, 0, 0, 130, 131, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr4C` is addressed. -/
def encT4C (a b c d : Fin 4) : Nat :=
  a.1 * 64 +
    b.1 * 16 +
    c.1 * 4 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank4C (a b c d : Fin 4) : Fin 132 :=
  ⟨min (rankArr4C.getD (encT4C a b c d) 0) 131, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end4C (i : Fin 132) : Magma (Fin 4) := Magma.mk (mem4C i)

theorem end4C_isEndo (i : Fin 132) (j : Fin 4) : (end4C i).IsEndo (endE4C j) := by
  revert i j; native_decide

theorem end4C_not_isEndo (i : Fin 132) (j : Fin 252) : ¬ (end4C i).IsEndo (endX4C j) := by
  revert i j; native_decide

/-- `rank4C` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem4C` for the index would be a comparison per tuple and
member. -/
theorem mem_rank4C (a b c d : Fin 4)
    (h : Magma.isExact (tab4C a b c d) endE4C endX4C = true) :
    mem4C (rank4C a b c d) = tab4C a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `132` listed
members. -/
theorem mem_of_isExact4C (a b c d : Fin 4)
    (h : Magma.isExact (tab4C a b c d) endE4C endX4C = true) :
    ∃ i, mem4C i = tab4C a b c d :=
  ⟨_, mem_rank4C a b c d h⟩

/-- A magma on `Fin 4` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end4C`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact4C` turns that into a member index. -/
theorem exists_end4C {M : Magma (Fin 4)} (hE : ∀ j, M.IsEndo (endE4C j))
    (hX : ∀ j, ¬ M.IsEndo (endX4C j)) : ∃ i, end4C i = M := by
  have hP : ∀ i, M.IsEndo (permE4C i) := by
    intro i; rw [permE4C_eq_endE4C]; exact hE (uidx4C i)
  have hop : M.op = Magma.transport permE4C tr4C (fun i ↦ M.op (rep4C i).1 (rep4C i).2) :=
    Magma.op_eq_transport (rep := rep4C) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE4C) (idx := stabIdx4C0) (a := (rep4C 0).1) (b := (rep4C 0).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE4C) (idx := stabIdx4C1) (a := (rep4C 1).1) (b := (rep4C 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE4C) (idx := stabIdx4C2) (a := (rep4C 2).1) (b := (rep4C 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE4C) (idx := stabIdx4C3) (a := (rep4C 3).1) (b := (rep4C 3).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec4C a b c d = fun i ↦ M.op (rep4C i).1 (rep4C i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tab4C a b c d = M.op := by
    rw [tab4C_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab4C a b c d) endE4C endX4C = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExact4C a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose endomorphism
monoid is exactly the order-`4` monoid of `Magma.endE4C`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end4C {L L' : Law.NatMagmaLaw} {i : Fin 132}
    (hsrc : @satisfies _ (Fin 4) (Magma.end4C i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.end4C j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end4C i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end4C
    (fun k ↦ (Magma.end4C_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end4C_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
