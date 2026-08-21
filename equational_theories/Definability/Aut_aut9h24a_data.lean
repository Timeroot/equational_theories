import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 24 on Fin 9

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 54675 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 24 on Fin 9 -/

namespace aut9h24a

/-- The 24 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 3, 2, 1, 4, 5, 7, 6, 8], #[0, 6, 2, 7, 8, 5, 3, 1, 4], #[0, 7, 2, 6, 8, 5, 1, 3, 4], #[1, 0, 3, 2, 5, 4, 7, 6, 8], #[1, 2, 3, 0, 5, 4, 6, 7, 8], #[1, 6, 3, 7, 8, 4, 0, 2, 5], #[1, 7, 3, 6, 8, 4, 2, 0, 5], #[2, 1, 0, 3, 4, 5, 7, 6, 8], #[2, 3, 0, 1, 4, 5, 6, 7, 8], #[2, 6, 0, 7, 8, 5, 1, 3, 4], #[2, 7, 0, 6, 8, 5, 3, 1, 4], #[3, 0, 1, 2, 5, 4, 6, 7, 8], #[3, 2, 1, 0, 5, 4, 7, 6, 8], #[3, 6, 1, 7, 8, 4, 2, 0, 5], #[3, 7, 1, 6, 8, 4, 0, 2, 5], #[6, 0, 7, 2, 5, 8, 1, 3, 4], #[6, 1, 7, 3, 4, 8, 2, 0, 5], #[6, 2, 7, 0, 5, 8, 3, 1, 4], #[6, 3, 7, 1, 4, 8, 0, 2, 5], #[7, 0, 6, 2, 5, 8, 3, 1, 4], #[7, 1, 6, 3, 4, 8, 0, 2, 5], #[7, 2, 6, 0, 5, 8, 1, 3, 4], #[7, 3, 6, 1, 4, 8, 2, 0, 5]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 3, 2, 1, 4, 5, 7, 6, 8], #[0, 7, 2, 6, 8, 5, 1, 3, 4], #[0, 6, 2, 7, 8, 5, 3, 1, 4], #[1, 0, 3, 2, 5, 4, 7, 6, 8], #[3, 0, 1, 2, 5, 4, 6, 7, 8], #[6, 0, 7, 2, 5, 8, 1, 3, 4], #[7, 0, 6, 2, 5, 8, 3, 1, 4], #[2, 1, 0, 3, 4, 5, 7, 6, 8], #[2, 3, 0, 1, 4, 5, 6, 7, 8], #[2, 6, 0, 7, 8, 5, 1, 3, 4], #[2, 7, 0, 6, 8, 5, 3, 1, 4], #[1, 2, 3, 0, 5, 4, 6, 7, 8], #[3, 2, 1, 0, 5, 4, 7, 6, 8], #[7, 2, 6, 0, 5, 8, 1, 3, 4], #[6, 2, 7, 0, 5, 8, 3, 1, 4], #[1, 6, 3, 7, 8, 4, 0, 2, 5], #[7, 1, 6, 3, 4, 8, 0, 2, 5], #[3, 7, 1, 6, 8, 4, 0, 2, 5], #[6, 3, 7, 1, 4, 8, 0, 2, 5], #[1, 7, 3, 6, 8, 4, 2, 0, 5], #[6, 1, 7, 3, 4, 8, 2, 0, 5], #[3, 6, 1, 7, 8, 4, 2, 0, 5], #[7, 3, 6, 1, 4, 8, 2, 0, 5]]

def E (i : Fin 24) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 24) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (9 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 4], #[0, 5], #[4, 0], #[4, 1], #[4, 4], #[4, 5]]

def rep (i : Fin 9) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[1, 1], #[3, 0], #[4, 0], #[1, 2], #[1, 3], #[3, 2]], #[#[1, 4], #[0, 4], #[1, 5], #[2, 4], #[4, 4], #[3, 4], #[1, 6], #[1, 7], #[3, 6]], #[#[2, 8], #[1, 8], #[0, 8], #[1, 9], #[3, 8], #[4, 8], #[1, 10], #[1, 11], #[3, 10]], #[#[1, 12], #[2, 12], #[1, 13], #[0, 12], #[4, 12], #[3, 12], #[1, 14], #[1, 15], #[3, 14]], #[#[5, 0], #[6, 0], #[5, 8], #[6, 1], #[7, 0], #[8, 0], #[5, 17], #[5, 21], #[8, 17]], #[#[6, 4], #[5, 4], #[6, 5], #[5, 12], #[8, 4], #[7, 4], #[5, 16], #[5, 20], #[8, 16]], #[#[1, 16], #[1, 17], #[1, 18], #[1, 19], #[3, 17], #[3, 16], #[0, 16], #[2, 16], #[4, 16]], #[#[1, 20], #[1, 21], #[1, 22], #[1, 23], #[3, 21], #[3, 20], #[2, 20], #[0, 20], #[4, 20]], #[#[5, 2], #[5, 6], #[5, 10], #[5, 14], #[8, 6], #[8, 2], #[6, 2], #[6, 3], #[7, 2]]]

def tr (x y : Fin 9) : Fin 9 × Fin 24 := (⟨((trd[x.1]!)[y.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 24, Nat.mod_lt _ (by decide)⟩)

end aut9h24a

namespace aut9h24a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 9) : Fin 24 := ⟨zd[i.1]! % 24, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16, 20, 20, 20, 20], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], #[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16, 20, 20, 20, 20], #[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 17, 16, 17, 20, 21, 20, 21], #[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16, 20, 20, 20, 20], #[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 17, 16, 17, 20, 21, 20, 21], #[0, 1, 2, 3, 4, 5, 2, 3, 0, 1, 2, 3, 4, 5, 2, 3, 4, 0, 5, 1, 4, 0, 5, 1], #[0, 0, 2, 2, 4, 4, 2, 2, 0, 0, 2, 2, 4, 4, 2, 2, 4, 0, 4, 0, 4, 0, 4, 0], #[0, 0, 2, 2, 4, 4, 6, 6, 0, 0, 2, 2, 4, 4, 6, 6, 16, 17, 16, 17, 16, 17, 16, 17]]

def st (i : Fin 9) (j : Fin 24) : Fin 24 := ⟨(std[i.1]!)[j.1]! % 24, Nat.mod_lt _ (by decide)⟩

end aut9h24a

/-! ### The sources -/

/-- A model of equation 3364 on `Fin 9` invariant under aut9h24a. -/
def aut9h24aMd3364 : Array (Array Nat) := #[#[5, 8, 5, 8, 8, 5, 4, 4, 4], #[8, 4, 8, 4, 4, 8, 5, 5, 5], #[5, 8, 5, 8, 8, 5, 4, 4, 4], #[8, 4, 8, 4, 4, 8, 5, 5, 5], #[8, 4, 8, 4, 4, 8, 5, 5, 5], #[5, 8, 5, 8, 8, 5, 4, 4, 4], #[4, 5, 4, 5, 5, 4, 8, 8, 8], #[4, 5, 4, 5, 5, 4, 8, 8, 8], #[4, 5, 4, 5, 5, 4, 8, 8, 8]]

@[reducible]
def aut9h24aM3364 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h24aMd3364[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
