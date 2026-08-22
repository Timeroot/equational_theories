import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 3 on Fin 6

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 2176782336 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 3 on Fin 6 -/

namespace prn6h3a

/-- The 3 permutations of `Fin 6`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[1, 2, 0, 4, 5, 3], #[2, 0, 1, 5, 3, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[2, 0, 1, 5, 3, 4], #[1, 2, 0, 4, 5, 3]]

def E (i : Fin 3) (x : Fin 6) : Fin 6 := ⟨(Ed[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 3) (x : Fin 6) : Fin 6 := ⟨(Eid[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (12 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[3, 0], #[3, 1], #[3, 2], #[3, 3], #[3, 4], #[3, 5]]

def rep (i : Fin 12) : Fin 6 × Fin 6 := (⟨(repd[i.1]!)[0]! % 6, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0]], #[#[2, 1], #[0, 1], #[1, 1], #[5, 1], #[3, 1], #[4, 1]], #[#[1, 2], #[2, 2], #[0, 2], #[4, 2], #[5, 2], #[3, 2]], #[#[6, 0], #[7, 0], #[8, 0], #[9, 0], #[10, 0], #[11, 0]], #[#[8, 1], #[6, 1], #[7, 1], #[11, 1], #[9, 1], #[10, 1]], #[#[7, 2], #[8, 2], #[6, 2], #[10, 2], #[11, 2], #[9, 2]]]

def tr (x y : Fin 6) : Fin 12 × Fin 3 := (⟨((trd[x.1]!)[y.1]!)[0]! % 12, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 3, Nat.mod_lt _ (by decide)⟩)

end prn6h3a

namespace prn6h3a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 12) : Fin 3 := ⟨zd[i.1]! % 3, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2]]

def st (i : Fin 12) (j : Fin 3) : Fin 3 := ⟨(std[i.1]!)[j.1]! % 3, Nat.mod_lt _ (by decide)⟩

end prn6h3a

/-! ### The sources -/

/-- A model of equation 1480 on `Fin 6` invariant under prn6h3a. -/
def prn6h3aMd1480 : Array (Array Nat) := #[#[1, 4, 4, 2, 4, 1], #[5, 2, 5, 2, 0, 5], #[3, 3, 0, 3, 0, 1], #[3, 3, 4, 3, 0, 1], #[5, 4, 4, 2, 4, 1], #[5, 3, 5, 2, 0, 5]]

@[reducible]
def prn6h3aM1480 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(prn6h3aMd1480[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 1682 on `Fin 6` invariant under prn6h3a. -/
def prn6h3aMd1682 : Array (Array Nat) := #[#[3, 4, 2, 0, 0, 4], #[0, 4, 5, 5, 1, 1], #[3, 1, 5, 2, 3, 2], #[0, 4, 0, 3, 0, 4], #[1, 1, 5, 5, 4, 1], #[3, 2, 2, 2, 3, 5]]

@[reducible]
def prn6h3aM1682 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(prn6h3aMd1682[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 1719 on `Fin 6` invariant under prn6h3a. -/
def prn6h3aMd1719 : Array (Array Nat) := #[#[1, 0, 5, 4, 3, 2], #[3, 2, 1, 0, 5, 4], #[2, 4, 0, 5, 1, 3], #[0, 5, 4, 3, 2, 1], #[5, 1, 3, 2, 4, 0], #[4, 3, 2, 1, 0, 5]]

@[reducible]
def prn6h3aM1719 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(prn6h3aMd1719[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩
