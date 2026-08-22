import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 8 on Fin 9

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

/-! ### group of order 8 on Fin 9 -/

namespace prn9h8a

/-- The 8 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 2, 6, 1, 7, 3, 8, 5, 4], #[0, 3, 1, 5, 8, 7, 2, 4, 6], #[0, 4, 7, 8, 1, 6, 5, 2, 3], #[0, 5, 3, 7, 6, 4, 1, 8, 2], #[0, 6, 8, 2, 5, 1, 4, 3, 7], #[0, 7, 5, 4, 2, 8, 3, 6, 1], #[0, 8, 4, 6, 3, 2, 7, 1, 5]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 3, 1, 5, 8, 7, 2, 4, 6], #[0, 2, 6, 1, 7, 3, 8, 5, 4], #[0, 4, 7, 8, 1, 6, 5, 2, 3], #[0, 6, 8, 2, 5, 1, 4, 3, 7], #[0, 5, 3, 7, 6, 4, 1, 8, 2], #[0, 8, 4, 6, 3, 2, 7, 1, 5], #[0, 7, 5, 4, 2, 8, 3, 6, 1]]

def E (i : Fin 8) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 8) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (11 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

def rep (i : Fin 11) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7]], #[#[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0], #[7, 0], #[8, 0], #[9, 0], #[10, 0]], #[#[2, 1], #[5, 1], #[3, 1], #[7, 1], #[10, 1], #[9, 1], #[4, 1], #[6, 1], #[8, 1]], #[#[2, 2], #[4, 2], #[8, 2], #[3, 2], #[9, 2], #[5, 2], #[10, 2], #[7, 2], #[6, 2]], #[#[2, 3], #[6, 3], #[9, 3], #[10, 3], #[3, 3], #[8, 3], #[7, 3], #[4, 3], #[5, 3]], #[#[2, 4], #[8, 4], #[10, 4], #[4, 4], #[7, 4], #[3, 4], #[6, 4], #[5, 4], #[9, 4]], #[#[2, 5], #[7, 5], #[5, 5], #[9, 5], #[8, 5], #[6, 5], #[3, 5], #[10, 5], #[4, 5]], #[#[2, 6], #[10, 6], #[6, 6], #[8, 6], #[5, 6], #[4, 6], #[9, 6], #[3, 6], #[7, 6]], #[#[2, 7], #[9, 7], #[7, 7], #[6, 7], #[4, 7], #[10, 7], #[5, 7], #[8, 7], #[3, 7]]]

def tr (x y : Fin 9) : Fin 11 × Fin 8 := (⟨((trd[x.1]!)[y.1]!)[0]! % 11, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

end prn9h8a

namespace prn9h8a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 11) : Fin 8 := ⟨zd[i.1]! % 8, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 0, 0], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7]]

def st (i : Fin 11) (j : Fin 8) : Fin 8 := ⟨(std[i.1]!)[j.1]! % 8, Nat.mod_lt _ (by decide)⟩

end prn9h8a

/-! ### The sources -/

/-- A model of equation 467 on `Fin 9` invariant under prn9h8a. -/
def prn9h8aMd467 : Array (Array Nat) := #[#[0, 6, 8, 2, 5, 1, 4, 3, 7], #[8, 2, 3, 4, 1, 7, 6, 0, 5], #[4, 7, 6, 5, 3, 0, 1, 2, 8], #[6, 5, 2, 1, 0, 8, 7, 4, 3], #[3, 4, 0, 6, 7, 5, 2, 8, 1], #[2, 1, 4, 7, 8, 3, 5, 6, 0], #[7, 3, 5, 0, 4, 6, 8, 1, 2], #[1, 8, 7, 3, 2, 4, 0, 5, 6], #[5, 0, 1, 8, 6, 2, 3, 7, 4]]

@[reducible]
def prn9h8aM467 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(prn9h8aMd467[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
