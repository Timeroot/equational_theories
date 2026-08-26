import equational_theories.Definability.ExactEnd4

/-!
# The exact-endomorphism class `N` on `Fin 4`

One class of `Definability/ExactEnd4.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The group of units, of order `3`: `⟨(1 2 3)⟩`

`End(M)` is `7` maps, so `Aut(M)` -- its unit group -- is these `3` permutations, and the
magmas of the class are among the ones invariant under them. That is what makes the class
enumerable at all: the invariant operations are `6` orbit values rather than `16`
independent cells. -/

/-- The `3` elements of the group: `()`, `(1 2 3)`, `(1 3 2)`. -/
def pE4N0 : Fin 4 → Fin 4 := id
def pE4N1 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1
def pE4N2 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2

def permE4N : Fin 3 → Fin 4 → Fin 4
  | 0 => pE4N0
  | 1 => pE4N1
  | 2 => pE4N2

/-! ### The endomorphism monoid

`End(M)` is a submonoid of the `256` self-maps of `Fin 4`, so demanding a set of them and
forbidding all the others pins it exactly -- there is no analogue of the exact-`Aut` search for a
small set of subgroup representatives. `Magma.allMaps4` indexes the self-maps, digit by digit. -/

/-- Indices of the `7` self-maps that must be endomorphisms: `0000`, `1111`, `0231`, `0312`, `2222`,
`0123`, `3333` (each written as its list of values at `0, 1, ..., 3`). -/
def eidx4N : Fin 7 → Fin 256
  | 0 => 0
  | 1 => 85
  | 2 => 120
  | 3 => 156
  | 4 => 170
  | 5 => 228
  | 6 => 255

def endE4N (j : Fin 7) : Fin 4 → Fin 4 := allMaps4 (eidx4N j)

/-- Indices of the other `249`, which must not be endomorphisms. This is a table rather than a match
because nothing the kernel evaluates ever reads it: `endX` occurs only in `native_decide` goals and
under `Magma.isExact_iff`, which is a rewrite. -/
def xarr4N : Array Nat := #[
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
  51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
  119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138,
  139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158,
  159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178,
  179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197,
  198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216,
  217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 229, 230, 231, 232, 233, 234, 235, 236,
  237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]

def xidx4N (j : Fin 249) : Fin 256 :=
  ⟨min (xarr4N.getD j.1 0) 255, by omega⟩

def endX4N (j : Fin 249) : Fin 4 → Fin 4 := allMaps4 (xidx4N j)

/-- Where each element of the group sits among the demanded endomorphisms, so that the orbit-
transport classification can be run on the hypothesis `end4N` is given. -/
def uidx4N : Fin 3 → Fin 7
  | 0 => 5
  | 1 => 2
  | 2 => 3

theorem permE4N_eq_endE4N (i : Fin 3) : permE4N i = endE4N (uidx4N i) := by
  revert i; decide

/-- One representative per orbit of the group on the `16` cells; there are `6`, so an invariant
operation is `6` values. -/
def rep4N : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | 3 => (1, 1)
  | 4 => (1, 2)
  | 5 => (1, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def tr4N : Fin 4 → Fin 4 → Fin 6 × Fin 3
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 1)
  | 0, 3 => (1, 2)
  | 1, 0 => (2, 0)
  | 1, 1 => (3, 0)
  | 1, 2 => (4, 0)
  | 1, 3 => (5, 0)
  | 2, 0 => (2, 1)
  | 2, 1 => (5, 1)
  | 2, 2 => (3, 1)
  | 2, 3 => (4, 1)
  | 3, 0 => (2, 2)
  | 3, 1 => (4, 2)
  | 3, 2 => (5, 2)
  | 3, 3 => (3, 2)

/-- The `3` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdx4N0 : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
def val4N0 : Fin 1 → Fin 4
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `1`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4N1 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `2`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4N2 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `3`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4N3 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `4`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4N4 : Fin 1 → Fin 3
  | 0 => 0

/-- The one group element fixing both coordinates of orbit `5`'s representative, and hence its
value: they fix everything, so the orbit is unconstrained and indexed by `Fin 4`. -/
def stabIdx4N5 : Fin 1 → Fin 3
  | 0 => 0

/-- The `6` orbit values named by the family's arguments. -/
def dec4N (a : Fin 1) (b c d e f : Fin 4) : Fin 6 → Fin 4
  | 0 => val4N0 a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tab4N_eq_transport`). -/
def tab4N (a : Fin 1) (b c d e f : Fin 4) : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => val4N0 a
  | 0, 1 => b
  | 0, 2 => pE4N1 b
  | 0, 3 => pE4N2 b
  | 1, 0 => c
  | 1, 1 => d
  | 1, 2 => e
  | 1, 3 => f
  | 2, 0 => pE4N1 c
  | 2, 1 => pE4N1 f
  | 2, 2 => pE4N1 d
  | 2, 3 => pE4N1 e
  | 3, 0 => pE4N2 c
  | 3, 1 => pE4N2 e
  | 3, 2 => pE4N2 f
  | 3, 3 => pE4N2 d

theorem tab4N_eq_transport (a : Fin 1) (b c d e f : Fin 4) :
    tab4N a b c d e f = Magma.transport permE4N tr4N (dec4N a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `194` magmas on `Fin 4` whose endomorphism monoid is exactly this one, listed under one
index. Of the `1024` invariant tuples these are the ones the forbidden maps rule out; naming only
them keeps the exactness test off the hot path of a family scan. -/
def memRow4N0 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 0 0 1 0 1
  | 1 => tab4N 0 0 0 1 0 2
  | 2 => tab4N 0 0 0 1 0 3
  | 3 => tab4N 0 0 0 1 1 0
  | 4 => tab4N 0 0 0 1 2 0
  | 5 => tab4N 0 0 0 1 3 0
  | 6 => tab4N 0 0 1 1 0 1
  | 7 => tab4N 0 0 1 1 0 2
  | 8 => tab4N 0 0 1 1 0 3
  | 9 => tab4N 0 0 1 1 1 0
  | 10 => tab4N 0 0 1 1 2 0
  | 11 => tab4N 0 0 1 1 3 0
  | 12 => tab4N 0 0 2 1 0 0
  | _ => tab4N 0 0 2 1 0 1
def memRow4N1 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 0 2 1 0 2
  | 1 => tab4N 0 0 2 1 0 3
  | 2 => tab4N 0 0 2 1 1 0
  | 3 => tab4N 0 0 2 1 1 2
  | 4 => tab4N 0 0 2 1 1 3
  | 5 => tab4N 0 0 2 1 2 0
  | 6 => tab4N 0 0 2 1 2 1
  | 7 => tab4N 0 0 2 1 2 2
  | 8 => tab4N 0 0 2 1 2 3
  | 9 => tab4N 0 0 2 1 3 0
  | 10 => tab4N 0 0 2 1 3 1
  | 11 => tab4N 0 0 2 1 3 2
  | 12 => tab4N 0 0 2 1 3 3
  | _ => tab4N 0 0 3 1 0 0
def memRow4N2 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 0 3 1 0 1
  | 1 => tab4N 0 0 3 1 0 2
  | 2 => tab4N 0 0 3 1 0 3
  | 3 => tab4N 0 0 3 1 1 0
  | 4 => tab4N 0 0 3 1 1 2
  | 5 => tab4N 0 0 3 1 1 3
  | 6 => tab4N 0 0 3 1 2 0
  | 7 => tab4N 0 0 3 1 2 1
  | 8 => tab4N 0 0 3 1 2 2
  | 9 => tab4N 0 0 3 1 2 3
  | 10 => tab4N 0 0 3 1 3 0
  | 11 => tab4N 0 0 3 1 3 1
  | 12 => tab4N 0 0 3 1 3 2
  | _ => tab4N 0 0 3 1 3 3
def memRow4N3 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 1 0 1 0 1
  | 1 => tab4N 0 1 0 1 0 2
  | 2 => tab4N 0 1 0 1 0 3
  | 3 => tab4N 0 1 0 1 1 0
  | 4 => tab4N 0 1 0 1 2 0
  | 5 => tab4N 0 1 0 1 3 0
  | 6 => tab4N 0 1 1 1 0 1
  | 7 => tab4N 0 1 1 1 0 2
  | 8 => tab4N 0 1 1 1 0 3
  | 9 => tab4N 0 1 1 1 1 0
  | 10 => tab4N 0 1 1 1 2 0
  | 11 => tab4N 0 1 1 1 3 0
  | 12 => tab4N 0 1 2 1 0 0
  | _ => tab4N 0 1 2 1 0 1
def memRow4N4 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 1 2 1 0 2
  | 1 => tab4N 0 1 2 1 0 3
  | 2 => tab4N 0 1 2 1 1 0
  | 3 => tab4N 0 1 2 1 1 1
  | 4 => tab4N 0 1 2 1 1 2
  | 5 => tab4N 0 1 2 1 2 0
  | 6 => tab4N 0 1 2 1 2 2
  | 7 => tab4N 0 1 2 1 2 3
  | 8 => tab4N 0 1 2 1 3 0
  | 9 => tab4N 0 1 2 1 3 1
  | 10 => tab4N 0 1 2 1 3 2
  | 11 => tab4N 0 1 2 1 3 3
  | 12 => tab4N 0 1 3 1 0 0
  | _ => tab4N 0 1 3 1 0 1
def memRow4N5 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 1 3 1 0 2
  | 1 => tab4N 0 1 3 1 0 3
  | 2 => tab4N 0 1 3 1 1 0
  | 3 => tab4N 0 1 3 1 1 1
  | 4 => tab4N 0 1 3 1 1 2
  | 5 => tab4N 0 1 3 1 2 0
  | 6 => tab4N 0 1 3 1 2 2
  | 7 => tab4N 0 1 3 1 2 3
  | 8 => tab4N 0 1 3 1 3 0
  | 9 => tab4N 0 1 3 1 3 1
  | 10 => tab4N 0 1 3 1 3 2
  | 11 => tab4N 0 1 3 1 3 3
  | 12 => tab4N 0 2 0 1 0 0
  | _ => tab4N 0 2 0 1 0 1
def memRow4N6 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 2 0 1 0 2
  | 1 => tab4N 0 2 0 1 0 3
  | 2 => tab4N 0 2 0 1 1 0
  | 3 => tab4N 0 2 0 1 1 1
  | 4 => tab4N 0 2 0 1 1 2
  | 5 => tab4N 0 2 0 1 1 3
  | 6 => tab4N 0 2 0 1 2 0
  | 7 => tab4N 0 2 0 1 2 1
  | 8 => tab4N 0 2 0 1 2 2
  | 9 => tab4N 0 2 0 1 3 0
  | 10 => tab4N 0 2 0 1 3 1
  | 11 => tab4N 0 2 0 1 3 2
  | 12 => tab4N 0 2 0 1 3 3
  | _ => tab4N 0 2 1 1 0 0
def memRow4N7 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 2 1 1 0 1
  | 1 => tab4N 0 2 1 1 0 2
  | 2 => tab4N 0 2 1 1 0 3
  | 3 => tab4N 0 2 1 1 1 0
  | 4 => tab4N 0 2 1 1 1 1
  | 5 => tab4N 0 2 1 1 1 2
  | 6 => tab4N 0 2 1 1 2 0
  | 7 => tab4N 0 2 1 1 2 2
  | 8 => tab4N 0 2 1 1 2 3
  | 9 => tab4N 0 2 1 1 3 0
  | 10 => tab4N 0 2 1 1 3 1
  | 11 => tab4N 0 2 1 1 3 2
  | 12 => tab4N 0 2 1 1 3 3
  | _ => tab4N 0 2 2 1 0 0
def memRow4N8 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 2 2 1 0 1
  | 1 => tab4N 0 2 2 1 0 2
  | 2 => tab4N 0 2 2 1 0 3
  | 3 => tab4N 0 2 2 1 1 0
  | 4 => tab4N 0 2 2 1 1 1
  | 5 => tab4N 0 2 2 1 1 2
  | 6 => tab4N 0 2 2 1 2 0
  | 7 => tab4N 0 2 2 1 2 2
  | 8 => tab4N 0 2 2 1 2 3
  | 9 => tab4N 0 2 2 1 3 0
  | 10 => tab4N 0 2 2 1 3 1
  | 11 => tab4N 0 2 2 1 3 2
  | 12 => tab4N 0 2 2 1 3 3
  | _ => tab4N 0 2 3 1 0 0
def memRow4N9 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 2 3 1 0 1
  | 1 => tab4N 0 2 3 1 0 3
  | 2 => tab4N 0 2 3 1 1 0
  | 3 => tab4N 0 2 3 1 1 1
  | 4 => tab4N 0 2 3 1 1 2
  | 5 => tab4N 0 2 3 1 2 0
  | 6 => tab4N 0 2 3 1 2 2
  | 7 => tab4N 0 2 3 1 2 3
  | 8 => tab4N 0 2 3 1 3 0
  | 9 => tab4N 0 2 3 1 3 1
  | 10 => tab4N 0 2 3 1 3 2
  | 11 => tab4N 0 2 3 1 3 3
  | 12 => tab4N 0 3 0 1 0 0
  | _ => tab4N 0 3 0 1 0 1
def memRow4N10 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 3 0 1 0 2
  | 1 => tab4N 0 3 0 1 0 3
  | 2 => tab4N 0 3 0 1 1 0
  | 3 => tab4N 0 3 0 1 1 1
  | 4 => tab4N 0 3 0 1 1 2
  | 5 => tab4N 0 3 0 1 1 3
  | 6 => tab4N 0 3 0 1 2 0
  | 7 => tab4N 0 3 0 1 2 1
  | 8 => tab4N 0 3 0 1 2 2
  | 9 => tab4N 0 3 0 1 3 0
  | 10 => tab4N 0 3 0 1 3 1
  | 11 => tab4N 0 3 0 1 3 2
  | 12 => tab4N 0 3 0 1 3 3
  | _ => tab4N 0 3 1 1 0 0
def memRow4N11 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 3 1 1 0 1
  | 1 => tab4N 0 3 1 1 0 2
  | 2 => tab4N 0 3 1 1 0 3
  | 3 => tab4N 0 3 1 1 1 0
  | 4 => tab4N 0 3 1 1 1 1
  | 5 => tab4N 0 3 1 1 1 2
  | 6 => tab4N 0 3 1 1 2 0
  | 7 => tab4N 0 3 1 1 2 2
  | 8 => tab4N 0 3 1 1 2 3
  | 9 => tab4N 0 3 1 1 3 0
  | 10 => tab4N 0 3 1 1 3 1
  | 11 => tab4N 0 3 1 1 3 2
  | 12 => tab4N 0 3 1 1 3 3
  | _ => tab4N 0 3 2 1 0 0
def memRow4N12 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 3 2 1 0 1
  | 1 => tab4N 0 3 2 1 0 2
  | 2 => tab4N 0 3 2 1 0 3
  | 3 => tab4N 0 3 2 1 1 0
  | 4 => tab4N 0 3 2 1 1 1
  | 5 => tab4N 0 3 2 1 1 2
  | 6 => tab4N 0 3 2 1 2 0
  | 7 => tab4N 0 3 2 1 2 2
  | 8 => tab4N 0 3 2 1 2 3
  | 9 => tab4N 0 3 2 1 3 1
  | 10 => tab4N 0 3 2 1 3 2
  | 11 => tab4N 0 3 2 1 3 3
  | 12 => tab4N 0 3 3 1 0 0
  | _ => tab4N 0 3 3 1 0 1
def memRow4N13 : Fin 14 → Fin 4 → Fin 4 → Fin 4
  | 0 => tab4N 0 3 3 1 0 2
  | 1 => tab4N 0 3 3 1 0 3
  | 2 => tab4N 0 3 3 1 1 0
  | 3 => tab4N 0 3 3 1 1 1
  | 4 => tab4N 0 3 3 1 1 2
  | 5 => tab4N 0 3 3 1 2 0
  | 6 => tab4N 0 3 3 1 2 2
  | 7 => tab4N 0 3 3 1 2 3
  | 8 => tab4N 0 3 3 1 3 0
  | 9 => tab4N 0 3 3 1 3 1
  | 10 => tab4N 0 3 3 1 3 2
  | _ => tab4N 0 3 3 1 3 3
def mem4N (i : Fin 194) : Fin 4 → Fin 4 → Fin 4 :=
  match (i.1 / 14 : Nat) with
  | 0 => memRow4N0 ⟨i.1 % 14, by omega⟩
  | 1 => memRow4N1 ⟨i.1 % 14, by omega⟩
  | 2 => memRow4N2 ⟨i.1 % 14, by omega⟩
  | 3 => memRow4N3 ⟨i.1 % 14, by omega⟩
  | 4 => memRow4N4 ⟨i.1 % 14, by omega⟩
  | 5 => memRow4N5 ⟨i.1 % 14, by omega⟩
  | 6 => memRow4N6 ⟨i.1 % 14, by omega⟩
  | 7 => memRow4N7 ⟨i.1 % 14, by omega⟩
  | 8 => memRow4N8 ⟨i.1 % 14, by omega⟩
  | 9 => memRow4N9 ⟨i.1 % 14, by omega⟩
  | 10 => memRow4N10 ⟨i.1 % 14, by omega⟩
  | 11 => memRow4N11 ⟨i.1 % 14, by omega⟩
  | 12 => memRow4N12 ⟨i.1 % 14, by omega⟩
  | _ => memRow4N13 ⟨i.1 % 14, by omega⟩

/-- Which of the `194` members a given invariant tuple is, so that `mem_of_isExact4N` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArr4N : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 7, 8, 9, 0, 0, 0, 10, 0, 0, 0, 11, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 14, 15, 16, 0, 17, 18, 19, 20, 21,
  22, 23, 24, 25, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 28, 29, 30, 31, 0, 32,
  33, 34, 35, 36, 37, 38, 39, 40, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 43,
  44, 45, 0, 0, 0, 46, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  48, 49, 50, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 54, 55, 56, 57, 58, 59, 60, 0, 61, 0, 62, 63, 64, 65, 66, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 68, 69, 70, 71, 72, 73, 74, 0, 75, 0, 76, 77, 78, 79, 80, 81, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 0, 93, 94, 95, 96,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 98, 99, 100, 101, 102, 103, 0, 104, 0, 105,
  106, 107, 108, 109, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 112, 113, 114,
  115, 116, 117, 0, 118, 0, 119, 120, 121, 122, 123, 124, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 125, 126, 0, 127, 128, 129, 130, 0, 131, 0, 132, 133, 134, 135, 136, 137, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 0,
  149, 150, 151, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 154, 155, 156, 157,
  158, 159, 0, 160, 0, 161, 162, 163, 164, 165, 166, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 167, 168, 169, 170, 171, 172, 173, 0, 174, 0, 175, 176, 0, 177, 178, 179, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 181, 182, 183, 184, 185, 186, 0, 187, 0, 188, 189, 190, 191,
  192, 193, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArr4N` is addressed. -/
def encT4N (a : Fin 1) (b c d e f : Fin 4) : Nat :=
  a.1 * 1024 +
    b.1 * 256 +
    c.1 * 64 +
    d.1 * 16 +
    e.1 * 4 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rank4N (a : Fin 1) (b c d e f : Fin 4) : Fin 194 :=
  ⟨min (rankArr4N.getD (encT4N a b c d e f) 0) 193, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end4N (i : Fin 194) : Magma (Fin 4) := Magma.mk (mem4N i)

theorem end4N_isEndo (i : Fin 194) (j : Fin 7) : (end4N i).IsEndo (endE4N j) := by
  revert i j; native_decide

theorem end4N_not_isEndo (i : Fin 194) (j : Fin 249) : ¬ (end4N i).IsEndo (endX4N j) := by
  revert i j; native_decide

/-- `rank4N` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `mem4N` for the index would be a comparison per tuple and
member. -/
theorem mem_rank4N (a : Fin 1) (b c d e f : Fin 4)
    (h : Magma.isExact (tab4N a b c d e f) endE4N endX4N = true) :
    mem4N (rank4N a b c d e f) = tab4N a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple whose endomorphism monoid really is this one names one of the `194` listed
members. -/
theorem mem_of_isExact4N (a : Fin 1) (b c d e f : Fin 4)
    (h : Magma.isExact (tab4N a b c d e f) endE4N endX4N = true) :
    ∃ i, mem4N i = tab4N a b c d e f :=
  ⟨_, mem_rank4N a b c d e f h⟩

/-- A magma on `Fin 4` admitting every demanded map and none of the forbidden ones *is* a member of
`Magma.end4N`. The demanded maps include the group, so its values at the orbit representatives name
an invariant tuple, and `mem_of_isExact4N` turns that into a member index. -/
theorem exists_end4N {M : Magma (Fin 4)} (hE : ∀ j, M.IsEndo (endE4N j))
    (hX : ∀ j, ¬ M.IsEndo (endX4N j)) : ∃ i, end4N i = M := by
  have hP : ∀ i, M.IsEndo (permE4N i) := by
    intro i; rw [permE4N_eq_endE4N]; exact hE (uidx4N i)
  have hop : M.op = Magma.transport permE4N tr4N (fun i ↦ M.op (rep4N i).1 (rep4N i).2) :=
    Magma.op_eq_transport (rep := rep4N) hP (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permE4N) (idx := stabIdx4N0) (a := (rep4N 0).1) (b := (rep4N 0).2)
    (val := val4N0) hP (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permE4N) (idx := stabIdx4N1) (a := (rep4N 1).1) (b := (rep4N 1).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permE4N) (idx := stabIdx4N2) (a := (rep4N 2).1) (b := (rep4N 2).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permE4N) (idx := stabIdx4N3) (a := (rep4N 3).1) (b := (rep4N 3).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permE4N) (idx := stabIdx4N4) (a := (rep4N 4).1) (b := (rep4N 4).2)
    (val := id) hP (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permE4N) (idx := stabIdx4N5) (a := (rep4N 5).1) (b := (rep4N 5).2)
    (val := id) hP (by decide) (by decide)
  have hdec : dec4N a b c d e f = fun i ↦ M.op (rep4N i).1 (rep4N i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tab4N a b c d e f = M.op := by
    rw [tab4N_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tab4N a b c d e f) endE4N endX4N = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExact4N a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 4`.** If `L'` has a model on `Fin 4` whose endomorphism
monoid is exactly the order-`7` monoid of `Magma.endE4N`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end4N {L L' : Law.NatMagmaLaw} {i : Fin 194}
    (hsrc : @satisfies _ (Fin 4) (Magma.end4N i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 4) (Magma.end4N j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end4N i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end4N
    (fun k ↦ (Magma.end4N_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end4N_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
