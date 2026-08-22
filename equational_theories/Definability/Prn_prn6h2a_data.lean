import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 2 on Fin 6

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 101559956668416 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 2 on Fin 6 -/

namespace prn6h2a

/-- The 2 permutations of `Fin 6`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[1, 0, 3, 2, 5, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[1, 0, 3, 2, 5, 4]]

def E (i : Fin 2) (x : Fin 6) : Fin 6 := ⟨(Ed[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 2) (x : Fin 6) : Fin 6 := ⟨(Eid[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (18 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[2, 0], #[2, 1], #[2, 2], #[2, 3], #[2, 4], #[2, 5], #[4, 0], #[4, 1], #[4, 2], #[4, 3], #[4, 4], #[4, 5]]

def rep (i : Fin 18) : Fin 6 × Fin 6 := (⟨(repd[i.1]!)[0]! % 6, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0]], #[#[1, 1], #[0, 1], #[3, 1], #[2, 1], #[5, 1], #[4, 1]], #[#[6, 0], #[7, 0], #[8, 0], #[9, 0], #[10, 0], #[11, 0]], #[#[7, 1], #[6, 1], #[9, 1], #[8, 1], #[11, 1], #[10, 1]], #[#[12, 0], #[13, 0], #[14, 0], #[15, 0], #[16, 0], #[17, 0]], #[#[13, 1], #[12, 1], #[15, 1], #[14, 1], #[17, 1], #[16, 1]]]

def tr (x y : Fin 6) : Fin 18 × Fin 2 := (⟨((trd[x.1]!)[y.1]!)[0]! % 18, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 2, Nat.mod_lt _ (by decide)⟩)

end prn6h2a

namespace prn6h2a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 18) : Fin 2 := ⟨zd[i.1]! % 2, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 1]]

def st (i : Fin 18) (j : Fin 2) : Fin 2 := ⟨(std[i.1]!)[j.1]! % 2, Nat.mod_lt _ (by decide)⟩

end prn6h2a

/-! ### The sources -/

/-- A model of equation 1480 on `Fin 6` invariant under prn6h2a. -/
def prn6h2aMd1480 : Array (Array Nat) := #[#[3, 2, 3, 2, 2, 3], #[3, 2, 3, 2, 2, 3], #[3, 4, 1, 1, 4, 3], #[5, 2, 0, 0, 2, 5], #[3, 4, 1, 1, 4, 3], #[5, 2, 0, 0, 2, 5]]

@[reducible]
def prn6h2aM1480 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(prn6h2aMd1480[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 3269 on `Fin 6` invariant under prn6h2a. -/
def prn6h2aMd3269 : Array (Array Nat) := #[#[4, 5, 0, 5, 0, 2], #[4, 5, 4, 1, 3, 1], #[0, 5, 4, 5, 4, 0], #[4, 1, 4, 5, 1, 5], #[0, 5, 4, 0, 4, 0], #[4, 1, 1, 5, 1, 5]]

@[reducible]
def prn6h2aM3269 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(prn6h2aMd3269[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 3279 on `Fin 6` invariant under prn6h2a. -/
def prn6h2aMd3279 : Array (Array Nat) := #[#[4, 2, 5, 2, 4, 0], #[3, 5, 3, 4, 1, 5], #[5, 0, 4, 0, 4, 2], #[1, 4, 1, 5, 3, 5], #[5, 0, 2, 0, 4, 0], #[1, 4, 1, 3, 1, 5]]

@[reducible]
def prn6h2aM3279 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(prn6h2aMd3279[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩
