import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 6 on Fin 9

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 2541865828329 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 6 on Fin 9 -/

namespace prn9h6a

/-- The 6 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 4, 6, 8, 1, 7, 2, 5, 3], #[5, 3, 8, 1, 6, 0, 4, 7, 2], #[5, 6, 4, 2, 3, 7, 8, 0, 1], #[7, 2, 1, 6, 8, 5, 3, 0, 4], #[7, 8, 3, 4, 2, 0, 1, 5, 6]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 4, 6, 8, 1, 7, 2, 5, 3], #[5, 3, 8, 1, 6, 0, 4, 7, 2], #[7, 8, 3, 4, 2, 0, 1, 5, 6], #[7, 2, 1, 6, 8, 5, 3, 0, 4], #[5, 6, 4, 2, 3, 7, 8, 0, 1]]

def E (i : Fin 6) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 6) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (14 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 5], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

def rep (i : Fin 14) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[1, 1], #[4, 0], #[2, 1], #[4, 1], #[3, 1]], #[#[5, 0], #[6, 0], #[7, 0], #[8, 0], #[9, 0], #[10, 0], #[11, 0], #[12, 0], #[13, 0]], #[#[12, 4], #[7, 4], #[6, 4], #[11, 4], #[13, 4], #[10, 4], #[8, 4], #[5, 4], #[9, 4]], #[#[10, 2], #[8, 2], #[13, 2], #[6, 2], #[11, 2], #[5, 2], #[9, 2], #[12, 2], #[7, 2]], #[#[5, 1], #[9, 1], #[11, 1], #[13, 1], #[6, 1], #[12, 1], #[7, 1], #[10, 1], #[8, 1]], #[#[4, 2], #[3, 2], #[3, 3], #[1, 2], #[2, 3], #[0, 2], #[1, 3], #[4, 3], #[2, 2]], #[#[12, 3], #[13, 3], #[8, 3], #[9, 3], #[7, 3], #[5, 3], #[6, 3], #[10, 3], #[11, 3]], #[#[4, 5], #[2, 4], #[1, 4], #[2, 5], #[3, 5], #[4, 4], #[3, 4], #[0, 4], #[1, 5]], #[#[10, 5], #[11, 5], #[9, 5], #[7, 5], #[8, 5], #[12, 5], #[13, 5], #[5, 5], #[6, 5]]]

def tr (x y : Fin 9) : Fin 14 × Fin 6 := (⟨((trd[x.1]!)[y.1]!)[0]! % 14, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

end prn9h6a

namespace prn9h6a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 14) : Fin 6 := ⟨zd[i.1]! % 6, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 2, 2, 4, 4], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5]]

def st (i : Fin 14) (j : Fin 6) : Fin 6 := ⟨(std[i.1]!)[j.1]! % 6, Nat.mod_lt _ (by decide)⟩

end prn9h6a

/-! ### The sources -/

/-- A model of equation 667 on `Fin 9` invariant under prn9h6a. -/
def prn9h6aMd667 : Array (Array Nat) := #[#[0, 6, 7, 1, 2, 8, 5, 3, 4], #[8, 4, 1, 3, 5, 0, 7, 2, 6], #[1, 2, 8, 0, 3, 7, 6, 4, 5], #[5, 1, 4, 6, 7, 2, 0, 8, 3], #[3, 7, 5, 2, 1, 6, 4, 0, 8], #[2, 3, 6, 4, 0, 5, 8, 1, 7], #[4, 8, 2, 7, 6, 1, 3, 5, 0], #[6, 0, 3, 5, 8, 4, 2, 7, 1], #[7, 5, 0, 8, 4, 3, 1, 6, 2]]

@[reducible]
def prn9h6aM667 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(prn9h6aMd667[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
