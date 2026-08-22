import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 8 on Fin 8

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 268435456 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 8 on Fin 8 -/

namespace prn8h8a

/-- The 8 permutations of `Fin 8`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 3, 2, 1, 4, 7, 6, 5], #[1, 0, 3, 2, 5, 4, 7, 6], #[1, 2, 3, 0, 5, 6, 7, 4], #[2, 1, 0, 3, 6, 5, 4, 7], #[2, 3, 0, 1, 6, 7, 4, 5], #[3, 0, 1, 2, 7, 4, 5, 6], #[3, 2, 1, 0, 7, 6, 5, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 3, 2, 1, 4, 7, 6, 5], #[1, 0, 3, 2, 5, 4, 7, 6], #[3, 0, 1, 2, 7, 4, 5, 6], #[2, 1, 0, 3, 6, 5, 4, 7], #[2, 3, 0, 1, 6, 7, 4, 5], #[1, 2, 3, 0, 5, 6, 7, 4], #[3, 2, 1, 0, 7, 6, 5, 4]]

def E (i : Fin 8) (x : Fin 8) : Fin 8 := ⟨(Ed[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 8) (x : Fin 8) : Fin 8 := ⟨(Eid[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (12 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 4], #[0, 5], #[0, 6], #[4, 0], #[4, 1], #[4, 2], #[4, 4], #[4, 5], #[4, 6]]

def rep (i : Fin 12) : Fin 8 × Fin 8 := (⟨(repd[i.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[1, 1], #[3, 0], #[4, 0], #[5, 0], #[4, 1]], #[#[1, 2], #[0, 2], #[1, 3], #[2, 2], #[4, 2], #[3, 2], #[4, 3], #[5, 2]], #[#[2, 4], #[1, 4], #[0, 4], #[1, 5], #[5, 4], #[4, 4], #[3, 4], #[4, 5]], #[#[1, 6], #[2, 6], #[1, 7], #[0, 6], #[4, 6], #[5, 6], #[4, 7], #[3, 6]], #[#[6, 0], #[7, 0], #[8, 0], #[7, 1], #[9, 0], #[10, 0], #[11, 0], #[10, 1]], #[#[7, 2], #[6, 2], #[7, 3], #[8, 2], #[10, 2], #[9, 2], #[10, 3], #[11, 2]], #[#[8, 4], #[7, 4], #[6, 4], #[7, 5], #[11, 4], #[10, 4], #[9, 4], #[10, 5]], #[#[7, 6], #[8, 6], #[7, 7], #[6, 6], #[10, 6], #[11, 6], #[10, 7], #[9, 6]]]

def tr (x y : Fin 8) : Fin 12 × Fin 8 := (⟨((trd[x.1]!)[y.1]!)[0]! % 12, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

end prn8h8a

namespace prn8h8a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 12) : Fin 8 := ⟨zd[i.1]! % 8, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 2, 2, 4, 4, 6, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 0, 2, 2, 4, 4, 6, 6], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 0, 2, 2, 4, 4, 6, 6]]

def st (i : Fin 12) (j : Fin 8) : Fin 8 := ⟨(std[i.1]!)[j.1]! % 8, Nat.mod_lt _ (by decide)⟩

end prn8h8a

/-! ### The sources -/

/-- A model of equation 1480 on `Fin 8` invariant under prn8h8a. -/
def prn8h8aMd1480 : Array (Array Nat) := #[#[0, 5, 6, 7, 2, 0, 0, 0], #[4, 1, 6, 7, 1, 3, 1, 1], #[4, 5, 2, 7, 2, 2, 0, 2], #[4, 5, 6, 3, 3, 3, 3, 1], #[0, 5, 6, 7, 6, 0, 0, 0], #[4, 1, 6, 7, 1, 7, 1, 1], #[4, 5, 2, 7, 2, 2, 4, 2], #[4, 5, 6, 3, 3, 3, 3, 5]]

@[reducible]
def prn8h8aM1480 : Magma (Fin 8) := Magma.mk fun x y ↦ ⟨(prn8h8aMd1480[x.1]!)[y.1]! % 8, Nat.mod_lt _ (by decide)⟩
