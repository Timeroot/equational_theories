import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 36 on Fin 9

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 81 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 36 on Fin 9 -/

namespace aut9h36a

/-- The 36 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 3, 7, 8, 5, 2, 1, 4, 6], #[0, 6, 5, 1, 7, 4, 8, 2, 3], #[0, 8, 4, 6, 2, 7, 3, 5, 1], #[1, 0, 3, 2, 5, 4, 7, 6, 8], #[1, 2, 6, 8, 4, 3, 0, 5, 7], #[1, 7, 4, 0, 6, 5, 8, 3, 2], #[1, 8, 5, 7, 3, 6, 2, 4, 0], #[2, 1, 8, 6, 3, 4, 5, 0, 7], #[2, 5, 4, 1, 0, 3, 7, 8, 6], #[2, 6, 0, 7, 4, 8, 1, 3, 5], #[2, 7, 3, 5, 8, 0, 6, 4, 1], #[3, 0, 8, 7, 2, 5, 4, 1, 6], #[3, 4, 5, 0, 1, 2, 6, 8, 7], #[3, 6, 2, 4, 8, 1, 7, 5, 0], #[3, 7, 1, 6, 5, 8, 0, 2, 4], #[4, 3, 0, 5, 2, 1, 8, 6, 7], #[4, 5, 6, 7, 1, 0, 3, 2, 8], #[4, 7, 2, 8, 0, 6, 5, 1, 3], #[4, 8, 1, 3, 6, 2, 7, 0, 5], #[5, 2, 1, 4, 3, 0, 8, 7, 6], #[5, 4, 7, 6, 0, 1, 2, 3, 8], #[5, 6, 3, 8, 1, 7, 4, 0, 2], #[5, 8, 0, 2, 7, 3, 6, 1, 4], #[6, 0, 1, 5, 4, 7, 2, 8, 3], #[6, 2, 7, 0, 8, 4, 3, 1, 5], #[6, 3, 4, 2, 1, 8, 5, 7, 0], #[6, 5, 8, 3, 7, 1, 0, 4, 2], #[7, 1, 0, 4, 5, 6, 3, 8, 2], #[7, 2, 5, 3, 0, 8, 4, 6, 1], #[7, 3, 6, 1, 8, 5, 2, 0, 4], #[7, 4, 8, 2, 6, 0, 1, 5, 3], #[8, 0, 6, 4, 7, 2, 5, 3, 1], #[8, 1, 7, 5, 6, 3, 4, 2, 0], #[8, 4, 3, 1, 2, 6, 0, 7, 5], #[8, 5, 2, 0, 3, 7, 1, 6, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 6, 5, 1, 7, 4, 8, 2, 3], #[0, 3, 7, 8, 5, 2, 1, 4, 6], #[0, 8, 4, 6, 2, 7, 3, 5, 1], #[1, 0, 3, 2, 5, 4, 7, 6, 8], #[6, 0, 1, 5, 4, 7, 2, 8, 3], #[3, 0, 8, 7, 2, 5, 4, 1, 6], #[8, 0, 6, 4, 7, 2, 5, 3, 1], #[7, 1, 0, 4, 5, 6, 3, 8, 2], #[4, 3, 0, 5, 2, 1, 8, 6, 7], #[2, 6, 0, 7, 4, 8, 1, 3, 5], #[5, 8, 0, 2, 7, 3, 6, 1, 4], #[1, 7, 4, 0, 6, 5, 8, 3, 2], #[3, 4, 5, 0, 1, 2, 6, 8, 7], #[8, 5, 2, 0, 3, 7, 1, 6, 4], #[6, 2, 7, 0, 8, 4, 3, 1, 5], #[2, 5, 4, 1, 0, 3, 7, 8, 6], #[5, 4, 7, 6, 0, 1, 2, 3, 8], #[4, 7, 2, 8, 0, 6, 5, 1, 3], #[7, 2, 5, 3, 0, 8, 4, 6, 1], #[5, 2, 1, 4, 3, 0, 8, 7, 6], #[4, 5, 6, 7, 1, 0, 3, 2, 8], #[7, 4, 8, 2, 6, 0, 1, 5, 3], #[2, 7, 3, 5, 8, 0, 6, 4, 1], #[1, 2, 6, 8, 4, 3, 0, 5, 7], #[3, 7, 1, 6, 5, 8, 0, 2, 4], #[8, 4, 3, 1, 2, 6, 0, 7, 5], #[6, 5, 8, 3, 7, 1, 0, 4, 2], #[2, 1, 8, 6, 3, 4, 5, 0, 7], #[4, 8, 1, 3, 6, 2, 7, 0, 5], #[7, 3, 6, 1, 8, 5, 2, 0, 4], #[5, 6, 3, 8, 1, 7, 4, 0, 2], #[1, 8, 5, 7, 3, 6, 2, 4, 0], #[8, 1, 7, 5, 6, 3, 4, 2, 0], #[6, 3, 4, 2, 1, 8, 5, 7, 0], #[3, 6, 2, 4, 8, 1, 7, 5, 0]]

def E (i : Fin 36) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 36) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (3 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2]]

def rep (i : Fin 3) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[1, 1], #[2, 3], #[2, 2], #[1, 2], #[2, 1], #[1, 3]], #[#[1, 4], #[0, 4], #[1, 5], #[2, 4], #[2, 6], #[2, 7], #[2, 5], #[1, 6], #[1, 7]], #[#[2, 10], #[1, 8], #[0, 8], #[2, 11], #[2, 9], #[1, 9], #[1, 10], #[1, 11], #[2, 8]], #[#[1, 12], #[2, 15], #[2, 14], #[0, 12], #[1, 13], #[2, 13], #[1, 14], #[1, 15], #[2, 12]], #[#[2, 16], #[2, 19], #[2, 18], #[1, 16], #[0, 16], #[1, 17], #[2, 17], #[1, 18], #[1, 19]], #[#[2, 23], #[2, 20], #[1, 20], #[2, 22], #[1, 21], #[0, 20], #[1, 22], #[2, 21], #[1, 23]], #[#[1, 24], #[2, 24], #[1, 25], #[1, 26], #[2, 26], #[1, 27], #[0, 24], #[2, 25], #[2, 27]], #[#[2, 28], #[1, 28], #[1, 29], #[1, 30], #[1, 31], #[2, 29], #[2, 30], #[0, 28], #[2, 31]], #[#[1, 32], #[1, 33], #[2, 35], #[2, 34], #[1, 34], #[1, 35], #[2, 32], #[2, 33], #[0, 32]]]

def tr (x y : Fin 9) : Fin 3 × Fin 36 := (⟨((trd[x.1]!)[y.1]!)[0]! % 3, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 36, Nat.mod_lt _ (by decide)⟩)

end aut9h36a

namespace aut9h36a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0]

def z (i : Fin 3) : Fin 36 := ⟨zd[i.1]! % 36, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 32, 32, 32, 32], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]

def st (i : Fin 3) (j : Fin 36) : Fin 36 := ⟨(std[i.1]!)[j.1]! % 36, Nat.mod_lt _ (by decide)⟩

end aut9h36a

/-! ### The sources -/

/-- A model of equation 474 on `Fin 9` invariant under aut9h36a. -/
def aut9h36aMd474 : Array (Array Nat) := #[#[0, 2, 8, 7, 1, 3, 5, 6, 4], #[3, 1, 6, 8, 2, 0, 7, 4, 5], #[5, 8, 2, 1, 6, 4, 0, 3, 7], #[8, 4, 0, 3, 5, 7, 2, 1, 6], #[7, 5, 3, 0, 4, 6, 8, 2, 1], #[4, 6, 1, 2, 7, 5, 3, 8, 0], #[1, 3, 7, 4, 0, 8, 6, 5, 2], #[2, 0, 5, 6, 8, 1, 4, 7, 3], #[6, 7, 4, 5, 3, 2, 1, 0, 8]]

@[reducible]
def aut9h36aM474 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h36aMd474[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 1083 on `Fin 9` invariant under aut9h36a. -/
def aut9h36aMd1083 : Array (Array Nat) := #[#[0, 4, 6, 5, 3, 8, 7, 1, 2], #[5, 1, 4, 7, 8, 2, 0, 6, 3], #[1, 3, 2, 6, 7, 0, 4, 8, 5], #[2, 0, 7, 3, 1, 6, 8, 5, 4], #[8, 7, 5, 2, 4, 1, 3, 0, 6], #[6, 8, 3, 4, 0, 5, 1, 2, 7], #[4, 2, 8, 1, 5, 7, 6, 3, 0], #[3, 5, 0, 8, 6, 4, 2, 7, 1], #[7, 6, 1, 0, 2, 3, 5, 4, 8]]

@[reducible]
def aut9h36aM1083 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h36aMd1083[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 1286 on `Fin 9` invariant under aut9h36a. -/
def aut9h36aMd1286 : Array (Array Nat) := #[#[0, 4, 6, 5, 3, 8, 7, 1, 2], #[5, 1, 4, 7, 8, 2, 0, 6, 3], #[1, 3, 2, 6, 7, 0, 4, 8, 5], #[2, 0, 7, 3, 1, 6, 8, 5, 4], #[8, 7, 5, 2, 4, 1, 3, 0, 6], #[6, 8, 3, 4, 0, 5, 1, 2, 7], #[4, 2, 8, 1, 5, 7, 6, 3, 0], #[3, 5, 0, 8, 6, 4, 2, 7, 1], #[7, 6, 1, 0, 2, 3, 5, 4, 8]]

@[reducible]
def aut9h36aM1286 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h36aMd1286[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 4321 on `Fin 9` invariant under aut9h36a. -/
def aut9h36aMd4321 : Array (Array Nat) := #[#[0, 4, 6, 5, 3, 8, 7, 1, 2], #[5, 1, 4, 7, 8, 2, 0, 6, 3], #[1, 3, 2, 6, 7, 0, 4, 8, 5], #[2, 0, 7, 3, 1, 6, 8, 5, 4], #[8, 7, 5, 2, 4, 1, 3, 0, 6], #[6, 8, 3, 4, 0, 5, 1, 2, 7], #[4, 2, 8, 1, 5, 7, 6, 3, 0], #[3, 5, 0, 8, 6, 4, 2, 7, 1], #[7, 6, 1, 0, 2, 3, 5, 4, 8]]

@[reducible]
def aut9h36aM4321 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h36aMd4321[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 4443 on `Fin 9` invariant under aut9h36a. -/
def aut9h36aMd4443 : Array (Array Nat) := #[#[0, 4, 6, 5, 3, 8, 7, 1, 2], #[5, 1, 4, 7, 8, 2, 0, 6, 3], #[1, 3, 2, 6, 7, 0, 4, 8, 5], #[2, 0, 7, 3, 1, 6, 8, 5, 4], #[8, 7, 5, 2, 4, 1, 3, 0, 6], #[6, 8, 3, 4, 0, 5, 1, 2, 7], #[4, 2, 8, 1, 5, 7, 6, 3, 0], #[3, 5, 0, 8, 6, 4, 2, 7, 1], #[7, 6, 1, 0, 2, 3, 5, 4, 8]]

@[reducible]
def aut9h36aM4443 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h36aMd4443[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
