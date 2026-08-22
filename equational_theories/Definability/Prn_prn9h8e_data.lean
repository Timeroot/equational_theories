import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 8 on Fin 9 (#5)

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 3486784401 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 8 on Fin 9 (#5) -/

namespace prn9h8e

/-- The 8 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[2, 1, 7, 0, 8, 6, 4, 3, 5], #[3, 1, 0, 7, 6, 8, 5, 2, 4], #[4, 1, 8, 6, 2, 3, 0, 5, 7], #[5, 1, 6, 8, 3, 2, 7, 4, 0], #[6, 1, 4, 5, 0, 7, 3, 8, 2], #[7, 1, 3, 2, 5, 4, 8, 0, 6], #[8, 1, 5, 4, 7, 0, 2, 6, 3]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[3, 1, 0, 7, 6, 8, 5, 2, 4], #[2, 1, 7, 0, 8, 6, 4, 3, 5], #[6, 1, 4, 5, 0, 7, 3, 8, 2], #[8, 1, 5, 4, 7, 0, 2, 6, 3], #[4, 1, 8, 6, 2, 3, 0, 5, 7], #[7, 1, 3, 2, 5, 4, 8, 0, 6], #[5, 1, 6, 8, 3, 2, 7, 4, 0]]

def E (i : Fin 8) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 8) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (11 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8], #[1, 0], #[1, 1]]

def rep (i : Fin 11) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0], #[7, 0], #[8, 0]], #[#[9, 0], #[10, 0], #[9, 1], #[9, 2], #[9, 3], #[9, 4], #[9, 5], #[9, 6], #[9, 7]], #[#[3, 1], #[1, 1], #[0, 1], #[7, 1], #[6, 1], #[8, 1], #[5, 1], #[2, 1], #[4, 1]], #[#[2, 2], #[1, 2], #[7, 2], #[0, 2], #[8, 2], #[6, 2], #[4, 2], #[3, 2], #[5, 2]], #[#[6, 3], #[1, 3], #[4, 3], #[5, 3], #[0, 3], #[7, 3], #[3, 3], #[8, 3], #[2, 3]], #[#[8, 4], #[1, 4], #[5, 4], #[4, 4], #[7, 4], #[0, 4], #[2, 4], #[6, 4], #[3, 4]], #[#[4, 5], #[1, 5], #[8, 5], #[6, 5], #[2, 5], #[3, 5], #[0, 5], #[5, 5], #[7, 5]], #[#[7, 6], #[1, 6], #[3, 6], #[2, 6], #[5, 6], #[4, 6], #[8, 6], #[0, 6], #[6, 6]], #[#[5, 7], #[1, 7], #[6, 7], #[8, 7], #[3, 7], #[2, 7], #[7, 7], #[4, 7], #[0, 7]]]

def tr (x y : Fin 9) : Fin 11 × Fin 8 := (⟨((trd[x.1]!)[y.1]!)[0]! % 11, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

end prn9h8e

namespace prn9h8e

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 11) : Fin 8 := ⟨zd[i.1]! % 8, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 0, 0, 0, 0, 0, 0, 0]]

def st (i : Fin 11) (j : Fin 8) : Fin 8 := ⟨(std[i.1]!)[j.1]! % 8, Nat.mod_lt _ (by decide)⟩

end prn9h8e

/-! ### The sources -/

/-- A model of equation 546 on `Fin 9` invariant under prn9h8e. -/
def prn9h8eMd546 : Array (Array Nat) := #[#[4, 7, 0, 1, 5, 2, 6, 8, 3], #[2, 1, 7, 0, 8, 6, 4, 3, 5], #[1, 3, 8, 5, 4, 0, 7, 2, 6], #[3, 2, 4, 6, 7, 5, 8, 1, 0], #[0, 5, 3, 8, 2, 7, 1, 6, 4], #[8, 4, 6, 2, 0, 3, 5, 7, 1], #[7, 8, 5, 3, 6, 1, 0, 4, 2], #[6, 0, 1, 7, 3, 4, 2, 5, 8], #[5, 6, 2, 4, 1, 8, 3, 0, 7]]

@[reducible]
def prn9h8eM546 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(prn9h8eMd546[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
