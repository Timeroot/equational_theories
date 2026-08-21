import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 8 on Fin 5

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 405 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 8 on Fin 5 -/

namespace aut5h8a

/-- The 8 permutations of `Fin 5`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4], #[0, 1, 2, 4, 3], #[0, 2, 1, 3, 4], #[0, 2, 1, 4, 3], #[0, 3, 4, 1, 2], #[0, 3, 4, 2, 1], #[0, 4, 3, 1, 2], #[0, 4, 3, 2, 1]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4], #[0, 1, 2, 4, 3], #[0, 2, 1, 3, 4], #[0, 2, 1, 4, 3], #[0, 3, 4, 1, 2], #[0, 4, 3, 1, 2], #[0, 3, 4, 2, 1], #[0, 4, 3, 2, 1]]

def E (i : Fin 8) (x : Fin 5) : Fin 5 := ⟨(Ed[i.1]!)[x.1]! % 5, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 8) (x : Fin 5) : Fin 5 := ⟨(Eid[i.1]!)[x.1]! % 5, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (6 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[1, 0], #[1, 1], #[1, 2], #[1, 3]]

def rep (i : Fin 6) : Fin 5 × Fin 5 := (⟨(repd[i.1]!)[0]! % 5, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 5, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[1, 2], #[1, 4], #[1, 6]], #[#[2, 0], #[3, 0], #[4, 0], #[5, 0], #[5, 1]], #[#[2, 2], #[4, 2], #[3, 2], #[5, 2], #[5, 3]], #[#[2, 4], #[5, 4], #[5, 5], #[3, 4], #[4, 4]], #[#[2, 6], #[5, 6], #[5, 7], #[4, 6], #[3, 6]]]

def tr (x y : Fin 5) : Fin 6 × Fin 8 := (⟨((trd[x.1]!)[y.1]!)[0]! % 6, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

end aut5h8a

namespace aut5h8a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0]

def z (i : Fin 6) : Fin 8 := ⟨zd[i.1]! % 8, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 1, 2, 3, 4, 5, 6, 7]]

def st (i : Fin 6) (j : Fin 8) : Fin 8 := ⟨(std[i.1]!)[j.1]! % 8, Nat.mod_lt _ (by decide)⟩

end aut5h8a

/-! ### The sources -/

/-- A model of equation 474 on `Fin 5` invariant under aut5h8a. -/
def aut5h8aMd474 : Array (Array Nat) := #[#[0, 2, 1, 4, 3], #[1, 0, 2, 3, 4], #[2, 1, 0, 3, 4], #[3, 1, 2, 0, 4], #[4, 1, 2, 3, 0]]

@[reducible]
def aut5h8aM474 : Magma (Fin 5) := Magma.mk fun x y ↦ ⟨(aut5h8aMd474[x.1]!)[y.1]! % 5, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 1685 on `Fin 5` invariant under aut5h8a. -/
def aut5h8aMd1685 : Array (Array Nat) := #[#[0, 2, 1, 4, 3], #[1, 0, 2, 3, 4], #[2, 1, 0, 3, 4], #[3, 1, 2, 0, 4], #[4, 1, 2, 3, 0]]

@[reducible]
def aut5h8aM1685 : Magma (Fin 5) := Magma.mk fun x y ↦ ⟨(aut5h8aMd1685[x.1]!)[y.1]! % 5, Nat.mod_lt _ (by decide)⟩
