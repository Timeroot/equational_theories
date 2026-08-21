import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 20 on Fin 7

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 27216 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 20 on Fin 7 -/

namespace aut7h20a

/-- The 20 permutations of `Fin 7`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6], #[0, 2, 4, 1, 3, 5, 6], #[0, 3, 1, 4, 2, 5, 6], #[0, 4, 3, 2, 1, 5, 6], #[1, 0, 4, 3, 2, 5, 6], #[1, 2, 3, 4, 0, 5, 6], #[1, 3, 0, 2, 4, 5, 6], #[1, 4, 2, 0, 3, 5, 6], #[2, 0, 3, 1, 4, 5, 6], #[2, 1, 0, 4, 3, 5, 6], #[2, 3, 4, 0, 1, 5, 6], #[2, 4, 1, 3, 0, 5, 6], #[3, 0, 2, 4, 1, 5, 6], #[3, 1, 4, 2, 0, 5, 6], #[3, 2, 1, 0, 4, 5, 6], #[3, 4, 0, 1, 2, 5, 6], #[4, 0, 1, 2, 3, 5, 6], #[4, 1, 3, 0, 2, 5, 6], #[4, 2, 0, 3, 1, 5, 6], #[4, 3, 2, 1, 0, 5, 6]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6], #[0, 3, 1, 4, 2, 5, 6], #[0, 2, 4, 1, 3, 5, 6], #[0, 4, 3, 2, 1, 5, 6], #[1, 0, 4, 3, 2, 5, 6], #[4, 0, 1, 2, 3, 5, 6], #[2, 0, 3, 1, 4, 5, 6], #[3, 0, 2, 4, 1, 5, 6], #[1, 3, 0, 2, 4, 5, 6], #[2, 1, 0, 4, 3, 5, 6], #[3, 4, 0, 1, 2, 5, 6], #[4, 2, 0, 3, 1, 5, 6], #[1, 4, 2, 0, 3, 5, 6], #[4, 1, 3, 0, 2, 5, 6], #[3, 2, 1, 0, 4, 5, 6], #[2, 3, 4, 0, 1, 5, 6], #[1, 2, 3, 4, 0, 5, 6], #[3, 1, 4, 2, 0, 5, 6], #[2, 4, 1, 3, 0, 5, 6], #[4, 3, 2, 1, 0, 5, 6]]

def E (i : Fin 20) (x : Fin 7) : Fin 7 := ⟨(Ed[i.1]!)[x.1]! % 7, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 20) (x : Fin 7) : Fin 7 := ⟨(Eid[i.1]!)[x.1]! % 7, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (10 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 5], #[0, 6], #[5, 0], #[5, 5], #[5, 6], #[6, 0], #[6, 5], #[6, 6]]

def rep (i : Fin 10) : Fin 7 × Fin 7 := (⟨(repd[i.1]!)[0]! % 7, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 7, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[2, 0], #[3, 0]], #[#[1, 4], #[0, 4], #[1, 5], #[1, 6], #[1, 7], #[2, 4], #[3, 4]], #[#[1, 8], #[1, 9], #[0, 8], #[1, 10], #[1, 11], #[2, 8], #[3, 8]], #[#[1, 12], #[1, 13], #[1, 14], #[0, 12], #[1, 15], #[2, 12], #[3, 12]], #[#[1, 16], #[1, 17], #[1, 18], #[1, 19], #[0, 16], #[2, 16], #[3, 16]], #[#[4, 0], #[4, 4], #[4, 8], #[4, 12], #[4, 16], #[5, 0], #[6, 0]], #[#[7, 0], #[7, 4], #[7, 8], #[7, 12], #[7, 16], #[8, 0], #[9, 0]]]

def tr (x y : Fin 7) : Fin 10 × Fin 20 := (⟨((trd[x.1]!)[y.1]!)[0]! % 10, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 20, Nat.mod_lt _ (by decide)⟩)

end aut7h20a

namespace aut7h20a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 10) : Fin 20 := ⟨zd[i.1]! % 20, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], #[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], #[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], #[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def st (i : Fin 10) (j : Fin 20) : Fin 20 := ⟨(std[i.1]!)[j.1]! % 20, Nat.mod_lt _ (by decide)⟩

end aut7h20a

/-! ### The sources -/

/-- A model of equation 1682 on `Fin 7` invariant under aut7h20a. -/
def aut7h20aMd1682 : Array (Array Nat) := #[#[0, 2, 4, 1, 3, 0, 5], #[4, 1, 3, 0, 2, 1, 5], #[3, 0, 2, 4, 1, 2, 5], #[2, 4, 1, 3, 0, 3, 5], #[1, 3, 0, 2, 4, 4, 5], #[6, 6, 6, 6, 6, 5, 6], #[0, 1, 2, 3, 4, 6, 5]]

@[reducible]
def aut7h20aM1682 : Magma (Fin 7) := Magma.mk fun x y ↦ ⟨(aut7h20aMd1682[x.1]!)[y.1]! % 7, Nat.mod_lt _ (by decide)⟩
