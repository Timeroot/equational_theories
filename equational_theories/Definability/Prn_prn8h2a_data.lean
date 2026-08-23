import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 2 on Fin 8

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 79228162514264337593543950336 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 2 on Fin 8 -/

namespace prn8h2a

/-- The 2 permutations of `Fin 8`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[1, 0, 3, 2, 5, 4, 7, 6]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[1, 0, 3, 2, 5, 4, 7, 6]]

def E (i : Fin 2) (x : Fin 8) : Fin 8 := ⟨(Ed[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 2) (x : Fin 8) : Fin 8 := ⟨(Eid[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (32 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[2, 0], #[2, 1], #[2, 2], #[2, 3], #[2, 4], #[2, 5], #[2, 6], #[2, 7], #[4, 0], #[4, 1], #[4, 2], #[4, 3], #[4, 4], #[4, 5], #[4, 6], #[4, 7], #[6, 0], #[6, 1], #[6, 2], #[6, 3], #[6, 4], #[6, 5], #[6, 6], #[6, 7]]

def rep (i : Fin 32) : Fin 8 × Fin 8 := (⟨(repd[i.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0], #[7, 0]], #[#[1, 1], #[0, 1], #[3, 1], #[2, 1], #[5, 1], #[4, 1], #[7, 1], #[6, 1]], #[#[8, 0], #[9, 0], #[10, 0], #[11, 0], #[12, 0], #[13, 0], #[14, 0], #[15, 0]], #[#[9, 1], #[8, 1], #[11, 1], #[10, 1], #[13, 1], #[12, 1], #[15, 1], #[14, 1]], #[#[16, 0], #[17, 0], #[18, 0], #[19, 0], #[20, 0], #[21, 0], #[22, 0], #[23, 0]], #[#[17, 1], #[16, 1], #[19, 1], #[18, 1], #[21, 1], #[20, 1], #[23, 1], #[22, 1]], #[#[24, 0], #[25, 0], #[26, 0], #[27, 0], #[28, 0], #[29, 0], #[30, 0], #[31, 0]], #[#[25, 1], #[24, 1], #[27, 1], #[26, 1], #[29, 1], #[28, 1], #[31, 1], #[30, 1]]]

def tr (x y : Fin 8) : Fin 32 × Fin 2 := (⟨((trd[x.1]!)[y.1]!)[0]! % 32, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 2, Nat.mod_lt _ (by decide)⟩)

end prn8h2a

namespace prn8h2a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 32) : Fin 2 := ⟨zd[i.1]! % 2, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1]]

def st (i : Fin 32) (j : Fin 2) : Fin 2 := ⟨(std[i.1]!)[j.1]! % 2, Nat.mod_lt _ (by decide)⟩

end prn8h2a

/-! ### The sources -/

/-- A model of equation 873 on `Fin 8` invariant under prn8h2a. -/
def prn8h2aMd873 : Array (Array Nat) := #[#[5, 1, 6, 3, 2, 4, 7, 0], #[0, 4, 2, 7, 5, 3, 1, 6], #[3, 5, 0, 6, 7, 2, 4, 1], #[4, 2, 7, 1, 3, 6, 0, 5], #[7, 3, 4, 0, 6, 1, 5, 2], #[2, 6, 1, 5, 0, 7, 3, 4], #[6, 0, 3, 4, 1, 5, 2, 7], #[1, 7, 5, 2, 4, 0, 6, 3]]

@[reducible]
def prn8h2aM873 : Magma (Fin 8) := Magma.mk fun x y ↦ ⟨(prn8h2aMd873[x.1]!)[y.1]! % 8, Nat.mod_lt _ (by decide)⟩
