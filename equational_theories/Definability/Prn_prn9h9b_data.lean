import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 9 on Fin 9 (#2)

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 387420489 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 9 on Fin 9 (#2) -/

namespace prn9h9b

/-- The 9 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[1, 4, 3, 7, 2, 8, 5, 6, 0], #[2, 3, 6, 5, 7, 1, 0, 8, 4], #[3, 7, 5, 8, 6, 4, 1, 0, 2], #[4, 2, 7, 6, 3, 0, 8, 5, 1], #[5, 8, 1, 4, 0, 7, 3, 2, 6], #[6, 5, 0, 1, 8, 3, 2, 4, 7], #[7, 6, 8, 0, 5, 2, 4, 1, 3], #[8, 0, 4, 2, 1, 6, 7, 3, 5]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[8, 0, 4, 2, 1, 6, 7, 3, 5], #[6, 5, 0, 1, 8, 3, 2, 4, 7], #[7, 6, 8, 0, 5, 2, 4, 1, 3], #[5, 8, 1, 4, 0, 7, 3, 2, 6], #[4, 2, 7, 6, 3, 0, 8, 5, 1], #[2, 3, 6, 5, 7, 1, 0, 8, 4], #[3, 7, 5, 8, 6, 4, 1, 0, 2], #[1, 4, 3, 7, 2, 8, 5, 6, 0]]

def E (i : Fin 9) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 9) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (9 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8]]

def rep (i : Fin 9) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0], #[7, 0], #[8, 0]], #[#[8, 1], #[0, 1], #[4, 1], #[2, 1], #[1, 1], #[6, 1], #[7, 1], #[3, 1], #[5, 1]], #[#[6, 2], #[5, 2], #[0, 2], #[1, 2], #[8, 2], #[3, 2], #[2, 2], #[4, 2], #[7, 2]], #[#[7, 3], #[6, 3], #[8, 3], #[0, 3], #[5, 3], #[2, 3], #[4, 3], #[1, 3], #[3, 3]], #[#[5, 4], #[8, 4], #[1, 4], #[4, 4], #[0, 4], #[7, 4], #[3, 4], #[2, 4], #[6, 4]], #[#[4, 5], #[2, 5], #[7, 5], #[6, 5], #[3, 5], #[0, 5], #[8, 5], #[5, 5], #[1, 5]], #[#[2, 6], #[3, 6], #[6, 6], #[5, 6], #[7, 6], #[1, 6], #[0, 6], #[8, 6], #[4, 6]], #[#[3, 7], #[7, 7], #[5, 7], #[8, 7], #[6, 7], #[4, 7], #[1, 7], #[0, 7], #[2, 7]], #[#[1, 8], #[4, 8], #[3, 8], #[7, 8], #[2, 8], #[8, 8], #[5, 8], #[6, 8], #[0, 8]]]

def tr (x y : Fin 9) : Fin 9 × Fin 9 := (⟨((trd[x.1]!)[y.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

end prn9h9b

namespace prn9h9b

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 9) : Fin 9 := ⟨zd[i.1]! % 9, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8]]

def st (i : Fin 9) (j : Fin 9) : Fin 9 := ⟨(std[i.1]!)[j.1]! % 9, Nat.mod_lt _ (by decide)⟩

end prn9h9b

/-! ### The sources -/

/-- A model of equation 501 on `Fin 9` invariant under prn9h9b. -/
def prn9h9bMd501 : Array (Array Nat) := #[#[5, 1, 4, 0, 7, 8, 2, 6, 3], #[7, 8, 6, 2, 4, 3, 5, 1, 0], #[6, 4, 1, 3, 5, 2, 7, 8, 0], #[1, 5, 8, 4, 2, 6, 0, 7, 3], #[1, 6, 2, 5, 0, 8, 4, 3, 7], #[2, 0, 3, 1, 5, 7, 4, 6, 8], #[8, 6, 0, 7, 2, 5, 3, 1, 4], #[7, 4, 3, 0, 8, 1, 6, 2, 5], #[0, 3, 8, 7, 1, 2, 5, 4, 6]]

@[reducible]
def prn9h9bM501 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(prn9h9bMd501[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
