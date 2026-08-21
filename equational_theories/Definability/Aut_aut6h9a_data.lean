import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 9 on Fin 6

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 26244 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 9 on Fin 6 -/

namespace aut6h9a

/-- The 9 permutations of `Fin 6`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 4, 5, 3], #[0, 1, 2, 5, 3, 4], #[1, 2, 0, 3, 4, 5], #[1, 2, 0, 4, 5, 3], #[1, 2, 0, 5, 3, 4], #[2, 0, 1, 3, 4, 5], #[2, 0, 1, 4, 5, 3], #[2, 0, 1, 5, 3, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 5, 3, 4], #[0, 1, 2, 4, 5, 3], #[2, 0, 1, 3, 4, 5], #[2, 0, 1, 5, 3, 4], #[2, 0, 1, 4, 5, 3], #[1, 2, 0, 3, 4, 5], #[1, 2, 0, 5, 3, 4], #[1, 2, 0, 4, 5, 3]]

def E (i : Fin 9) (x : Fin 6) : Fin 6 := ⟨(Ed[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 9) (x : Fin 6) : Fin 6 := ⟨(Eid[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (8 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[3, 0], #[3, 3], #[3, 4], #[3, 5]]

def rep (i : Fin 8) : Fin 6 × Fin 6 := (⟨(repd[i.1]!)[0]! % 6, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[3, 1], #[3, 2]], #[#[2, 3], #[0, 3], #[1, 3], #[3, 3], #[3, 4], #[3, 5]], #[#[1, 6], #[2, 6], #[0, 6], #[3, 6], #[3, 7], #[3, 8]], #[#[4, 0], #[4, 3], #[4, 6], #[5, 0], #[6, 0], #[7, 0]], #[#[4, 1], #[4, 4], #[4, 7], #[7, 1], #[5, 1], #[6, 1]], #[#[4, 2], #[4, 5], #[4, 8], #[6, 2], #[7, 2], #[5, 2]]]

def tr (x y : Fin 6) : Fin 8 × Fin 9 := (⟨((trd[x.1]!)[y.1]!)[0]! % 8, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

end aut6h9a

namespace aut6h9a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 8) : Fin 9 := ⟨zd[i.1]! % 9, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 3, 3, 3, 6, 6, 6], #[0, 0, 0, 3, 3, 3, 6, 6, 6], #[0, 0, 0, 3, 3, 3, 6, 6, 6], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 0, 1, 2, 0, 1, 2], #[0, 1, 2, 0, 1, 2, 0, 1, 2], #[0, 1, 2, 0, 1, 2, 0, 1, 2]]

def st (i : Fin 8) (j : Fin 9) : Fin 9 := ⟨(std[i.1]!)[j.1]! % 9, Nat.mod_lt _ (by decide)⟩

end aut6h9a

/-! ### The sources -/

/-- A model of equation 3355 on `Fin 6` invariant under aut6h9a. -/
def aut6h9aMd3355 : Array (Array Nat) := #[#[0, 0, 2, 0, 0, 0], #[0, 1, 1, 1, 1, 1], #[2, 1, 2, 2, 2, 2], #[0, 1, 2, 3, 3, 5], #[0, 1, 2, 3, 4, 4], #[0, 1, 2, 5, 4, 5]]

@[reducible]
def aut6h9aM3355 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(aut6h9aMd3355[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩
