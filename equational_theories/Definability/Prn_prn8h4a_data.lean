import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 4 on Fin 8

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 281474976710656 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 4 on Fin 8 -/

namespace prn8h4a

/-- The 4 permutations of `Fin 8`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[1, 2, 3, 0, 5, 6, 7, 4], #[2, 3, 0, 1, 6, 7, 4, 5], #[3, 0, 1, 2, 7, 4, 5, 6]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[3, 0, 1, 2, 7, 4, 5, 6], #[2, 3, 0, 1, 6, 7, 4, 5], #[1, 2, 3, 0, 5, 6, 7, 4]]

def E (i : Fin 4) (x : Fin 8) : Fin 8 := ⟨(Ed[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 4) (x : Fin 8) : Fin 8 := ⟨(Eid[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (16 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[4, 0], #[4, 1], #[4, 2], #[4, 3], #[4, 4], #[4, 5], #[4, 6], #[4, 7]]

def rep (i : Fin 16) : Fin 8 × Fin 8 := (⟨(repd[i.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0], #[7, 0]], #[#[3, 1], #[0, 1], #[1, 1], #[2, 1], #[7, 1], #[4, 1], #[5, 1], #[6, 1]], #[#[2, 2], #[3, 2], #[0, 2], #[1, 2], #[6, 2], #[7, 2], #[4, 2], #[5, 2]], #[#[1, 3], #[2, 3], #[3, 3], #[0, 3], #[5, 3], #[6, 3], #[7, 3], #[4, 3]], #[#[8, 0], #[9, 0], #[10, 0], #[11, 0], #[12, 0], #[13, 0], #[14, 0], #[15, 0]], #[#[11, 1], #[8, 1], #[9, 1], #[10, 1], #[15, 1], #[12, 1], #[13, 1], #[14, 1]], #[#[10, 2], #[11, 2], #[8, 2], #[9, 2], #[14, 2], #[15, 2], #[12, 2], #[13, 2]], #[#[9, 3], #[10, 3], #[11, 3], #[8, 3], #[13, 3], #[14, 3], #[15, 3], #[12, 3]]]

def tr (x y : Fin 8) : Fin 16 × Fin 4 := (⟨((trd[x.1]!)[y.1]!)[0]! % 16, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 4, Nat.mod_lt _ (by decide)⟩)

end prn8h4a

namespace prn8h4a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 16) : Fin 4 := ⟨zd[i.1]! % 4, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3]]

def st (i : Fin 16) (j : Fin 4) : Fin 4 := ⟨(std[i.1]!)[j.1]! % 4, Nat.mod_lt _ (by decide)⟩

end prn8h4a

/-! ### The sources -/

/-- A model of equation 680 on `Fin 8` invariant under prn8h4a. -/
def prn8h4aMd680 : Array (Array Nat) := #[#[0, 5, 4, 6, 3, 7, 2, 1], #[7, 1, 6, 5, 2, 0, 4, 3], #[6, 4, 2, 7, 0, 3, 1, 5], #[4, 7, 5, 3, 6, 1, 0, 2], #[2, 6, 1, 0, 5, 4, 3, 7], #[1, 3, 7, 2, 4, 6, 5, 0], #[3, 2, 0, 4, 1, 5, 7, 6], #[5, 0, 3, 1, 7, 2, 6, 4]]

@[reducible]
def prn8h4aM680 : Magma (Fin 8) := Magma.mk fun x y ↦ ⟨(prn8h4aMd680[x.1]!)[y.1]! % 8, Nat.mod_lt _ (by decide)⟩
