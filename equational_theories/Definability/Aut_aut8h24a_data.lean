import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 24 on Fin 8

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 4096 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 24 on Fin 8 -/

namespace aut8h24a

/-- The 24 permutations of `Fin 8`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 6, 7, 4, 5], #[0, 5, 2, 6, 3, 7, 4, 1], #[0, 5, 2, 6, 4, 1, 3, 7], #[0, 7, 2, 4, 3, 5, 6, 1], #[0, 7, 2, 4, 6, 1, 3, 5], #[1, 0, 3, 2, 4, 5, 6, 7], #[1, 0, 3, 2, 6, 7, 4, 5], #[1, 5, 3, 6, 2, 7, 4, 0], #[1, 5, 3, 6, 4, 0, 2, 7], #[1, 7, 3, 4, 2, 5, 6, 0], #[1, 7, 3, 4, 6, 0, 2, 5], #[5, 0, 6, 2, 3, 7, 4, 1], #[5, 0, 6, 2, 4, 1, 3, 7], #[5, 1, 6, 3, 2, 7, 4, 0], #[5, 1, 6, 3, 4, 0, 2, 7], #[5, 7, 6, 4, 2, 1, 3, 0], #[5, 7, 6, 4, 3, 0, 2, 1], #[7, 0, 4, 2, 3, 5, 6, 1], #[7, 0, 4, 2, 6, 1, 3, 5], #[7, 1, 4, 3, 2, 5, 6, 0], #[7, 1, 4, 3, 6, 0, 2, 5], #[7, 5, 4, 6, 2, 1, 3, 0], #[7, 5, 4, 6, 3, 0, 2, 1]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 6, 7, 4, 5], #[0, 7, 2, 4, 6, 1, 3, 5], #[0, 5, 2, 6, 4, 1, 3, 7], #[0, 7, 2, 4, 3, 5, 6, 1], #[0, 5, 2, 6, 3, 7, 4, 1], #[1, 0, 3, 2, 4, 5, 6, 7], #[1, 0, 3, 2, 6, 7, 4, 5], #[7, 0, 4, 2, 6, 1, 3, 5], #[5, 0, 6, 2, 4, 1, 3, 7], #[7, 0, 4, 2, 3, 5, 6, 1], #[5, 0, 6, 2, 3, 7, 4, 1], #[1, 7, 3, 4, 6, 0, 2, 5], #[1, 5, 3, 6, 4, 0, 2, 7], #[7, 1, 4, 3, 6, 0, 2, 5], #[5, 1, 6, 3, 4, 0, 2, 7], #[7, 5, 4, 6, 3, 0, 2, 1], #[5, 7, 6, 4, 3, 0, 2, 1], #[1, 7, 3, 4, 2, 5, 6, 0], #[1, 5, 3, 6, 2, 7, 4, 0], #[7, 1, 4, 3, 2, 5, 6, 0], #[5, 1, 6, 3, 2, 7, 4, 0], #[7, 5, 4, 6, 2, 1, 3, 0], #[5, 7, 6, 4, 2, 1, 3, 0]]

def E (i : Fin 24) (x : Fin 8) : Fin 8 := ⟨(Ed[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 24) (x : Fin 8) : Fin 8 := ⟨(Eid[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (8 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[2, 0], #[2, 1], #[2, 2], #[2, 3]]

def rep (i : Fin 8) : Fin 8 × Fin 8 := (⟨(repd[i.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[3, 4], #[1, 2], #[3, 2], #[1, 4]], #[#[1, 6], #[0, 6], #[3, 6], #[2, 6], #[3, 10], #[1, 8], #[3, 8], #[1, 10]], #[#[4, 0], #[5, 0], #[6, 0], #[7, 0], #[7, 4], #[5, 2], #[7, 2], #[5, 4]], #[#[5, 6], #[4, 6], #[7, 6], #[6, 6], #[7, 10], #[5, 8], #[7, 8], #[5, 10]], #[#[5, 18], #[5, 20], #[7, 18], #[7, 20], #[6, 18], #[5, 22], #[7, 22], #[4, 18]], #[#[1, 12], #[1, 14], #[3, 12], #[3, 14], #[3, 16], #[0, 12], #[2, 12], #[1, 16]], #[#[5, 12], #[5, 14], #[7, 12], #[7, 14], #[7, 16], #[4, 12], #[6, 12], #[5, 16]], #[#[1, 18], #[1, 20], #[3, 18], #[3, 20], #[2, 18], #[1, 22], #[3, 22], #[0, 18]]]

def tr (x y : Fin 8) : Fin 8 × Fin 24 := (⟨((trd[x.1]!)[y.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 24, Nat.mod_lt _ (by decide)⟩)

end aut8h24a

namespace aut8h24a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 8) : Fin 24 := ⟨zd[i.1]! % 24, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], #[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22], #[0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], #[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22], #[0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], #[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22], #[0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], #[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22]]

def st (i : Fin 8) (j : Fin 24) : Fin 24 := ⟨(std[i.1]!)[j.1]! % 24, Nat.mod_lt _ (by decide)⟩

end aut8h24a

/-! ### The sources -/

/-- A model of equation 3272 on `Fin 8` invariant under aut8h24a. -/
def aut8h24aMd3272 : Array (Array Nat) := #[#[0, 2, 0, 1, 7, 2, 5, 2], #[3, 1, 0, 1, 7, 3, 5, 3], #[0, 2, 0, 1, 7, 2, 5, 2], #[3, 1, 0, 1, 7, 3, 5, 3], #[4, 4, 0, 1, 7, 4, 5, 7], #[6, 6, 0, 1, 7, 5, 5, 6], #[6, 6, 0, 1, 7, 5, 5, 6], #[4, 4, 0, 1, 7, 4, 5, 7]]

@[reducible]
def aut8h24aM3272 : Magma (Fin 8) := Magma.mk fun x y ↦ ⟨(aut8h24aMd3272[x.1]!)[y.1]! % 8, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 3748 on `Fin 8` invariant under aut8h24a. -/
def aut8h24aMd3748 : Array (Array Nat) := #[#[0, 2, 0, 0, 0, 2, 0, 2], #[3, 1, 1, 1, 1, 3, 1, 3], #[0, 3, 0, 2, 2, 6, 2, 4], #[2, 1, 3, 1, 3, 6, 3, 4], #[2, 3, 4, 4, 7, 6, 4, 7], #[6, 6, 5, 5, 5, 5, 5, 6], #[2, 3, 6, 6, 6, 5, 5, 4], #[4, 4, 7, 7, 7, 4, 7, 7]]

@[reducible]
def aut8h24aM3748 : Magma (Fin 8) := Magma.mk fun x y ↦ ⟨(aut8h24aMd3748[x.1]!)[y.1]! % 8, Nat.mod_lt _ (by decide)⟩
