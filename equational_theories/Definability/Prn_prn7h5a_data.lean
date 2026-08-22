import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 5 on Fin 7

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 645657712 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 5 on Fin 7 -/

namespace prn7h5a

/-- The 5 permutations of `Fin 7`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6], #[2, 1, 4, 6, 3, 5, 0], #[3, 1, 6, 2, 0, 5, 4], #[4, 1, 3, 0, 6, 5, 2], #[6, 1, 0, 4, 2, 5, 3]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6], #[6, 1, 0, 4, 2, 5, 3], #[4, 1, 3, 0, 6, 5, 2], #[3, 1, 6, 2, 0, 5, 4], #[2, 1, 4, 6, 3, 5, 0]]

def E (i : Fin 5) (x : Fin 7) : Fin 7 := ⟨(Ed[i.1]!)[x.1]! % 7, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 5) (x : Fin 7) : Fin 7 := ⟨(Eid[i.1]!)[x.1]! % 7, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (13 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[1, 0], #[1, 1], #[1, 5], #[5, 0], #[5, 1], #[5, 5]]

def rep (i : Fin 13) : Fin 7 × Fin 7 := (⟨(repd[i.1]!)[0]! % 7, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 7, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0]], #[#[7, 0], #[8, 0], #[7, 1], #[7, 2], #[7, 3], #[9, 0], #[7, 4]], #[#[6, 1], #[1, 1], #[0, 1], #[4, 1], #[2, 1], #[5, 1], #[3, 1]], #[#[4, 2], #[1, 2], #[3, 2], #[0, 2], #[6, 2], #[5, 2], #[2, 2]], #[#[3, 3], #[1, 3], #[6, 3], #[2, 3], #[0, 3], #[5, 3], #[4, 3]], #[#[10, 0], #[11, 0], #[10, 1], #[10, 2], #[10, 3], #[12, 0], #[10, 4]], #[#[2, 4], #[1, 4], #[4, 4], #[6, 4], #[3, 4], #[5, 4], #[0, 4]]]

def tr (x y : Fin 7) : Fin 13 × Fin 5 := (⟨((trd[x.1]!)[y.1]!)[0]! % 13, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 5, Nat.mod_lt _ (by decide)⟩)

end prn7h5a

namespace prn7h5a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 13) : Fin 5 := ⟨zd[i.1]! % 5, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[0, 1, 2, 3, 4], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0]]

def st (i : Fin 13) (j : Fin 5) : Fin 5 := ⟨(std[i.1]!)[j.1]! % 5, Nat.mod_lt _ (by decide)⟩

end prn7h5a

/-! ### The sources -/

/-- A model of equation 481 on `Fin 7` invariant under prn7h5a. -/
def prn7h5aMd481 : Array (Array Nat) := #[#[1, 2, 6, 5, 4, 3, 0], #[6, 1, 0, 4, 2, 5, 3], #[2, 4, 1, 3, 0, 6, 5], #[0, 6, 5, 1, 3, 2, 4], #[5, 3, 4, 2, 1, 0, 6], #[4, 5, 3, 0, 6, 1, 2], #[3, 0, 2, 6, 5, 4, 1]]

@[reducible]
def prn7h5aM481 : Magma (Fin 7) := Magma.mk fun x y ↦ ⟨(prn7h5aMd481[x.1]!)[y.1]! % 7, Nat.mod_lt _ (by decide)⟩
