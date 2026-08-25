import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `K4` on `Fin 4`

One class of `Definability/ExactAut4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`4` group `⟨(0 1)(2 3), (0 2)(1 3)⟩` -/

/-- The `4` elements of the group: `()`, `(0 1)(2 3)`, `(0 2)(1 3)`, `(0 3)(1 2)`. -/
def pEK40 : Fin 4 → Fin 4 := id
def pEK41 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
def pEK42 : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
def pEK43 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0

def permEK4 : Fin 4 → Fin 4 → Fin 4
  | 0 => pEK40
  | 1 => pEK41
  | 2 => pEK42
  | 3 => pEK43

def permEinvK4 : Fin 4 → Fin 4 → Fin 4
  | 0 => pEK40
  | 1 => pEK41
  | 2 => pEK42
  | 3 => pEK43

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEK4 (i : Fin 4) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permEK4 i) (permEinvK4 i) (by revert i; decide)

/-- The `4` permutations that must *not* be automorphisms: `(1 2)`, `(0 1 3)`, `(0 3 2 1)`, `(0 3 1
2)`. Every subgroup properly containing the group above contains one of them, so a magma admitting
the group and not these has that group as its automorphism group exactly. -/
def pXK40 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pXK41 : Fin 4 → Fin 4 | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0
def pXK42 : Fin 4 → Fin 4 | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2
def pXK43 : Fin 4 → Fin 4 | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1
def pXK40inv : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
def pXK41inv : Fin 4 → Fin 4 | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1
def pXK42inv : Fin 4 → Fin 4 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0
def pXK43inv : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0

def permXK4 : Fin 4 → Fin 4 → Fin 4
  | 0 => pXK40
  | 1 => pXK41
  | 2 => pXK42
  | 3 => pXK43

def permXinvK4 : Fin 4 → Fin 4 → Fin 4
  | 0 => pXK40inv
  | 1 => pXK41inv
  | 2 => pXK42inv
  | 3 => pXK43inv

def eXK4 (i : Fin 4) : Equiv.Perm (Fin 4) :=
  Magma.permOf (permXK4 i) (permXinvK4 i) (by revert i; decide)

/-- One representative per orbit of the group on the `16` cells; there are `4`, so an invariant
operation is `4` values. -/
def repK4 : Fin 4 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trK4 : Fin 4 → Fin 4 → Fin 4 × Fin 4
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
def stabIdxK40 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxK41 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxK42 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdxK43 : Fin 1 → Fin 4
  | 0 => 0

/-- The `4` orbit values named by the family's arguments. -/
def decK4 (a b c d : Fin 4) : Fin 4 → Fin 4
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabK4_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabK4 (a b c d : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => a
  | 0, 1 => b
  | 0, 2 => c
  | 0, 3 => d
  | 1, 0 => pEK41 b
  | 1, 1 => pEK41 a
  | 1, 2 => pEK41 d
  | 1, 3 => pEK41 c
  | 2, 0 => pEK42 c
  | 2, 1 => pEK42 d
  | 2, 2 => pEK42 a
  | 2, 3 => pEK42 b
  | 3, 0 => pEK43 d
  | 3, 1 => pEK43 c
  | 3, 2 => pEK43 b
  | 3, 3 => pEK43 a

theorem tabK4_eq_transport (a b c d : Fin 4) :
    tabK4 a b c d = Magma.transport permEK4 trK4 (decK4 a b c d) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `210` magmas on `Fin 4` whose automorphism group is exactly this group, listed under one
index. Of the `256` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowK40 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 0 0 0 1
  | 1 => tabK4 0 0 0 2
  | 2 => tabK4 0 0 1 0
  | 3 => tabK4 0 0 1 2
  | 4 => tabK4 0 0 1 3
  | 5 => tabK4 0 0 2 1
  | 6 => tabK4 0 0 2 2
  | 7 => tabK4 0 0 3 0
  | 8 => tabK4 0 0 3 1
  | 9 => tabK4 0 0 3 3
  | 10 => tabK4 0 1 0 1
  | 11 => tabK4 0 1 0 2
  | 12 => tabK4 0 1 1 0
  | 13 => tabK4 0 1 1 2
  | _ => tabK4 0 1 1 3
def memRowK41 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 0 1 2 1
  | 1 => tabK4 0 1 2 2
  | 2 => tabK4 0 1 3 0
  | 3 => tabK4 0 1 3 1
  | 4 => tabK4 0 1 3 3
  | 5 => tabK4 0 2 0 0
  | 6 => tabK4 0 2 0 1
  | 7 => tabK4 0 2 0 3
  | 8 => tabK4 0 2 1 1
  | 9 => tabK4 0 2 1 2
  | 10 => tabK4 0 2 2 0
  | 11 => tabK4 0 2 2 1
  | 12 => tabK4 0 2 2 3
  | 13 => tabK4 0 2 3 0
  | _ => tabK4 0 2 3 2
def memRowK42 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 0 2 3 3
  | 1 => tabK4 0 3 0 0
  | 2 => tabK4 0 3 0 2
  | 3 => tabK4 0 3 0 3
  | 4 => tabK4 0 3 1 0
  | 5 => tabK4 0 3 1 1
  | 6 => tabK4 0 3 1 3
  | 7 => tabK4 0 3 2 0
  | 8 => tabK4 0 3 2 2
  | 9 => tabK4 0 3 2 3
  | 10 => tabK4 0 3 3 1
  | 11 => tabK4 0 3 3 2
  | 12 => tabK4 1 0 0 1
  | 13 => tabK4 1 0 0 2
  | _ => tabK4 1 0 0 3
def memRowK43 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 1 0 1 0
  | 1 => tabK4 1 0 1 2
  | 2 => tabK4 1 0 1 3
  | 3 => tabK4 1 0 2 0
  | 4 => tabK4 1 0 2 1
  | 5 => tabK4 1 0 2 2
  | 6 => tabK4 1 0 3 0
  | 7 => tabK4 1 0 3 1
  | 8 => tabK4 1 0 3 3
  | 9 => tabK4 1 1 0 1
  | 10 => tabK4 1 1 0 2
  | 11 => tabK4 1 1 0 3
  | 12 => tabK4 1 1 1 0
  | 13 => tabK4 1 1 1 2
  | _ => tabK4 1 1 1 3
def memRowK44 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 1 1 2 0
  | 1 => tabK4 1 1 2 1
  | 2 => tabK4 1 1 2 2
  | 3 => tabK4 1 1 3 0
  | 4 => tabK4 1 1 3 1
  | 5 => tabK4 1 1 3 3
  | 6 => tabK4 1 2 0 0
  | 7 => tabK4 1 2 0 1
  | 8 => tabK4 1 2 0 2
  | 9 => tabK4 1 2 0 3
  | 10 => tabK4 1 2 1 0
  | 11 => tabK4 1 2 1 1
  | 12 => tabK4 1 2 1 2
  | 13 => tabK4 1 2 1 3
  | _ => tabK4 1 2 2 0
def memRowK45 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 1 2 2 1
  | 1 => tabK4 1 2 2 2
  | 2 => tabK4 1 2 2 3
  | 3 => tabK4 1 2 3 0
  | 4 => tabK4 1 2 3 1
  | 5 => tabK4 1 2 3 2
  | 6 => tabK4 1 2 3 3
  | 7 => tabK4 1 3 0 0
  | 8 => tabK4 1 3 0 1
  | 9 => tabK4 1 3 0 2
  | 10 => tabK4 1 3 0 3
  | 11 => tabK4 1 3 1 0
  | 12 => tabK4 1 3 1 1
  | 13 => tabK4 1 3 1 2
  | _ => tabK4 1 3 1 3
def memRowK46 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 1 3 2 0
  | 1 => tabK4 1 3 2 1
  | 2 => tabK4 1 3 2 2
  | 3 => tabK4 1 3 2 3
  | 4 => tabK4 1 3 3 0
  | 5 => tabK4 1 3 3 1
  | 6 => tabK4 1 3 3 2
  | 7 => tabK4 1 3 3 3
  | 8 => tabK4 2 0 0 1
  | 9 => tabK4 2 0 0 2
  | 10 => tabK4 2 0 0 3
  | 11 => tabK4 2 0 1 0
  | 12 => tabK4 2 0 1 1
  | 13 => tabK4 2 0 1 2
  | _ => tabK4 2 0 1 3
def memRowK47 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 2 0 2 1
  | 1 => tabK4 2 0 2 2
  | 2 => tabK4 2 0 2 3
  | 3 => tabK4 2 0 3 0
  | 4 => tabK4 2 0 3 1
  | 5 => tabK4 2 0 3 2
  | 6 => tabK4 2 0 3 3
  | 7 => tabK4 2 1 0 0
  | 8 => tabK4 2 1 0 1
  | 9 => tabK4 2 1 0 2
  | 10 => tabK4 2 1 1 0
  | 11 => tabK4 2 1 1 1
  | 12 => tabK4 2 1 1 2
  | 13 => tabK4 2 1 1 3
  | _ => tabK4 2 1 2 0
def memRowK48 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 2 1 2 1
  | 1 => tabK4 2 1 2 2
  | 2 => tabK4 2 1 3 0
  | 3 => tabK4 2 1 3 1
  | 4 => tabK4 2 1 3 2
  | 5 => tabK4 2 1 3 3
  | 6 => tabK4 2 2 0 0
  | 7 => tabK4 2 2 0 1
  | 8 => tabK4 2 2 0 3
  | 9 => tabK4 2 2 1 0
  | 10 => tabK4 2 2 1 1
  | 11 => tabK4 2 2 1 2
  | 12 => tabK4 2 2 1 3
  | 13 => tabK4 2 2 2 0
  | _ => tabK4 2 2 2 1
def memRowK49 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 2 2 2 3
  | 1 => tabK4 2 2 3 0
  | 2 => tabK4 2 2 3 1
  | 3 => tabK4 2 2 3 2
  | 4 => tabK4 2 2 3 3
  | 5 => tabK4 2 3 0 0
  | 6 => tabK4 2 3 0 2
  | 7 => tabK4 2 3 0 3
  | 8 => tabK4 2 3 1 0
  | 9 => tabK4 2 3 1 1
  | 10 => tabK4 2 3 1 2
  | 11 => tabK4 2 3 1 3
  | 12 => tabK4 2 3 2 0
  | 13 => tabK4 2 3 2 2
  | _ => tabK4 2 3 2 3
def memRowK410 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 2 3 3 0
  | 1 => tabK4 2 3 3 1
  | 2 => tabK4 2 3 3 2
  | 3 => tabK4 2 3 3 3
  | 4 => tabK4 3 0 0 1
  | 5 => tabK4 3 0 0 2
  | 6 => tabK4 3 0 1 0
  | 7 => tabK4 3 0 1 1
  | 8 => tabK4 3 0 1 2
  | 9 => tabK4 3 0 1 3
  | 10 => tabK4 3 0 2 0
  | 11 => tabK4 3 0 2 1
  | 12 => tabK4 3 0 2 2
  | 13 => tabK4 3 0 2 3
  | _ => tabK4 3 0 3 0
def memRowK411 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 3 0 3 1
  | 1 => tabK4 3 0 3 2
  | 2 => tabK4 3 0 3 3
  | 3 => tabK4 3 1 0 0
  | 4 => tabK4 3 1 0 1
  | 5 => tabK4 3 1 0 2
  | 6 => tabK4 3 1 0 3
  | 7 => tabK4 3 1 1 0
  | 8 => tabK4 3 1 1 1
  | 9 => tabK4 3 1 1 2
  | 10 => tabK4 3 1 1 3
  | 11 => tabK4 3 1 2 1
  | 12 => tabK4 3 1 2 2
  | 13 => tabK4 3 1 3 0
  | _ => tabK4 3 1 3 1
def memRowK412 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 3 1 3 2
  | 1 => tabK4 3 1 3 3
  | 2 => tabK4 3 2 0 0
  | 3 => tabK4 3 2 0 1
  | 4 => tabK4 3 2 0 2
  | 5 => tabK4 3 2 0 3
  | 6 => tabK4 3 2 1 1
  | 7 => tabK4 3 2 1 2
  | 8 => tabK4 3 2 2 0
  | 9 => tabK4 3 2 2 1
  | 10 => tabK4 3 2 2 2
  | 11 => tabK4 3 2 2 3
  | 12 => tabK4 3 2 3 0
  | 13 => tabK4 3 2 3 1
  | _ => tabK4 3 2 3 2
def memRowK413 : Fin 15 → Fin 4 → Fin 4 → Fin 4
  | 0 => tabK4 3 2 3 3
  | 1 => tabK4 3 3 0 0
  | 2 => tabK4 3 3 0 1
  | 3 => tabK4 3 3 0 2
  | 4 => tabK4 3 3 0 3
  | 5 => tabK4 3 3 1 0
  | 6 => tabK4 3 3 1 1
  | 7 => tabK4 3 3 1 2
  | 8 => tabK4 3 3 1 3
  | 9 => tabK4 3 3 2 0
  | 10 => tabK4 3 3 2 1
  | 11 => tabK4 3 3 2 2
  | 12 => tabK4 3 3 2 3
  | 13 => tabK4 3 3 3 1
  | _ => tabK4 3 3 3 2
def memK4 (i : Fin 210) : Fin 4 → Fin 4 → Fin 4 :=
  match (i.1 / 15 : Nat) with
  | 0 => memRowK40 ⟨i.1 % 15, by omega⟩
  | 1 => memRowK41 ⟨i.1 % 15, by omega⟩
  | 2 => memRowK42 ⟨i.1 % 15, by omega⟩
  | 3 => memRowK43 ⟨i.1 % 15, by omega⟩
  | 4 => memRowK44 ⟨i.1 % 15, by omega⟩
  | 5 => memRowK45 ⟨i.1 % 15, by omega⟩
  | 6 => memRowK46 ⟨i.1 % 15, by omega⟩
  | 7 => memRowK47 ⟨i.1 % 15, by omega⟩
  | 8 => memRowK48 ⟨i.1 % 15, by omega⟩
  | 9 => memRowK49 ⟨i.1 % 15, by omega⟩
  | 10 => memRowK410 ⟨i.1 % 15, by omega⟩
  | 11 => memRowK411 ⟨i.1 % 15, by omega⟩
  | 12 => memRowK412 ⟨i.1 % 15, by omega⟩
  | _ => memRowK413 ⟨i.1 % 15, by omega⟩

/-- Which of the `210` members a given invariant tuple is, so that `mem_of_isExactK4` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrK4 : Array Nat := #[
  0, 0, 1, 0, 2, 0, 3, 4, 0, 5, 6, 0, 7, 8, 0, 9, 0, 10, 11, 0, 12, 0, 13, 14, 0, 15, 16, 0, 17,
  18, 0, 19, 20, 21, 0, 22, 0, 23, 24, 0, 25, 26, 0, 27, 28, 0, 29, 30, 31, 0, 32, 33, 34, 35, 0,
  36, 37, 0, 38, 39, 0, 40, 41, 0, 0, 42, 43, 44, 45, 0, 46, 47, 48, 49, 50, 0, 51, 52, 0, 53, 0,
  54, 55, 56, 57, 0, 58, 59, 60, 61, 62, 0, 63, 64, 0, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 0,
  98, 99, 100, 101, 102, 103, 104, 0, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 0, 115,
  116, 117, 118, 119, 120, 121, 0, 122, 123, 124, 125, 126, 127, 0, 128, 129, 130, 131, 132, 133,
  134, 0, 135, 136, 137, 138, 139, 140, 0, 141, 142, 143, 144, 145, 146, 147, 0, 148, 149, 150,
  151, 152, 153, 0, 154, 155, 0, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168,
  169, 170, 171, 172, 173, 174, 175, 0, 176, 177, 0, 178, 179, 180, 181, 182, 183, 184, 185, 0,
  186, 187, 0, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
  204, 205, 206, 207, 0, 208, 209, 0]

/-- The arguments as one mixed-radix index, which is how `rankArrK4` is addressed. -/
def encTK4 (a b c d : Fin 4) : Nat :=
  a.1 * 64 +
    b.1 * 16 +
    c.1 * 4 +
    d.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankK4 (a b c d : Fin 4) : Fin 210 :=
  ⟨min (rankArrK4.getD (encTK4 a b c d) 0) 209, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactK4 (i : Fin 210) : Magma (Fin 4) := Magma.mk (memK4 i)

theorem exactK4_isEndo (i : Fin 210) (j : Fin 4) : (exactK4 i).IsEndo ⇑(eEK4 j) := by
  simp only [eEK4, coe_permOf]; revert i j; native_decide

theorem exactK4_not_isEndo (i : Fin 210) (j : Fin 4) : ¬ (exactK4 i).IsEndo ⇑(eXK4 j) := by
  simp only [eXK4, coe_permOf]; revert i j; native_decide

/-- `rankK4` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memK4` for the index would be a comparison per tuple and
member. -/
theorem mem_rankK4 (a b c d : Fin 4)
    (h : Magma.isExact (tabK4 a b c d) permEK4 permXK4 = true) :
    memK4 (rankK4 a b c d) = tabK4 a b c d := by
  revert h; revert a b c d; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `210`
listed members. -/
theorem mem_of_isExactK4 (a b c d : Fin 4)
    (h : Magma.isExact (tabK4 a b c d) permEK4 permXK4 = true) :
    ∃ i, memK4 i = tabK4 a b c d :=
  ⟨_, mem_rankK4 a b c d h⟩

/-- A magma on `Fin 4` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactK4`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactK4` turns that into a member index. -/
theorem exists_exactK4 {M : Magma (Fin 4)} (hE : ∀ i, M.IsEndo ⇑(eEK4 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXK4 i)) : ∃ i, exactK4 i = M := by
  simp only [eEK4, coe_permOf] at hE
  simp only [eXK4, coe_permOf] at hX
  have hop : M.op = Magma.transport permEK4 trK4 (fun i ↦ M.op (repK4 i).1 (repK4 i).2) :=
    Magma.op_eq_transport (rep := repK4) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEK4) (idx := stabIdxK40) (a := (repK4 0).1) (b := (repK4 0).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEK4) (idx := stabIdxK41) (a := (repK4 1).1) (b := (repK4 1).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permEK4) (idx := stabIdxK42) (a := (repK4 2).1) (b := (repK4 2).2)
    (val := id) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permEK4) (idx := stabIdxK43) (a := (repK4 3).1) (b := (repK4 3).2)
    (val := id) hE (by decide) (by decide)
  have hdec : decK4 a b c d = fun i ↦ M.op (repK4 i).1 (repK4 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have key : tabK4 a b c d = M.op := by
    rw [tabK4_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabK4 a b c d) permEK4 permXK4 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactK4 a b c d hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose automorphism
group is exactly the order-`4` group of `Magma.permEK4`, and no such magma satisfies `L`, then `L`
is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactK4 {L L' : Law.NatMagmaLaw} {i : Fin 210}
    (hsrc : @satisfies _ (Fin 4) (Magma.exactK4 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.exactK4 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactK4 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactK4
    (fun k ↦ (Magma.exactK4_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactK4_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
