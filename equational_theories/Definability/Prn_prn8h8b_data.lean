import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 8 on Fin 8 (#2)

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 16777216 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 8 on Fin 8 (#2) -/

namespace prn8h8b

/-- The 8 permutations of `Fin 8`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 7, 6, 5, 4], #[3, 2, 1, 0, 6, 7, 4, 5], #[4, 6, 7, 5, 0, 3, 1, 2], #[5, 7, 6, 4, 1, 2, 0, 3], #[6, 4, 5, 7, 3, 0, 2, 1], #[7, 5, 4, 6, 2, 1, 3, 0]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[1, 0, 3, 2, 5, 4, 7, 6], #[2, 3, 0, 1, 7, 6, 5, 4], #[3, 2, 1, 0, 6, 7, 4, 5], #[4, 6, 7, 5, 0, 3, 1, 2], #[6, 4, 5, 7, 3, 0, 2, 1], #[5, 7, 6, 4, 1, 2, 0, 3], #[7, 5, 4, 6, 2, 1, 3, 0]]

def E (i : Fin 8) (x : Fin 8) : Fin 8 := ⟨(Ed[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 8) (x : Fin 8) : Fin 8 := ⟨(Eid[i.1]!)[x.1]! % 8, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (8 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7]]

def rep (i : Fin 8) : Fin 8 × Fin 8 := (⟨(repd[i.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0], #[6, 0], #[7, 0]], #[#[1, 1], #[0, 1], #[3, 1], #[2, 1], #[5, 1], #[4, 1], #[7, 1], #[6, 1]], #[#[2, 2], #[3, 2], #[0, 2], #[1, 2], #[7, 2], #[6, 2], #[5, 2], #[4, 2]], #[#[3, 3], #[2, 3], #[1, 3], #[0, 3], #[6, 3], #[7, 3], #[4, 3], #[5, 3]], #[#[4, 4], #[6, 4], #[7, 4], #[5, 4], #[0, 4], #[3, 4], #[1, 4], #[2, 4]], #[#[6, 5], #[4, 5], #[5, 5], #[7, 5], #[3, 5], #[0, 5], #[2, 5], #[1, 5]], #[#[5, 6], #[7, 6], #[6, 6], #[4, 6], #[1, 6], #[2, 6], #[0, 6], #[3, 6]], #[#[7, 7], #[5, 7], #[4, 7], #[6, 7], #[2, 7], #[1, 7], #[3, 7], #[0, 7]]]

def tr (x y : Fin 8) : Fin 8 × Fin 8 := (⟨((trd[x.1]!)[y.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 8, Nat.mod_lt _ (by decide)⟩)

end prn8h8b

namespace prn8h8b

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 8) : Fin 8 := ⟨zd[i.1]! % 8, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7]]

def st (i : Fin 8) (j : Fin 8) : Fin 8 := ⟨(std[i.1]!)[j.1]! % 8, Nat.mod_lt _ (by decide)⟩

end prn8h8b

/-! ### The sources -/

/-- A model of equation 1480 on `Fin 8` invariant under prn8h8b. -/
def prn8h8bMd1480 : Array (Array Nat) := #[#[7, 6, 6, 7, 3, 3, 7, 6], #[7, 6, 6, 7, 2, 2, 7, 6], #[5, 4, 4, 5, 5, 4, 1, 1], #[5, 4, 4, 5, 5, 4, 0, 0], #[5, 2, 1, 5, 2, 2, 1, 1], #[3, 4, 4, 0, 3, 3, 0, 0], #[7, 2, 1, 7, 2, 2, 1, 1], #[3, 6, 6, 0, 3, 3, 0, 0]]

@[reducible]
def prn8h8bM1480 : Magma (Fin 8) := Magma.mk fun x y ↦ ⟨(prn8h8bMd1480[x.1]!)[y.1]! % 8, Nat.mod_lt _ (by decide)⟩
