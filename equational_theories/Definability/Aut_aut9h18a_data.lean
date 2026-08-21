import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 18 on Fin 9

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 6561 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 18 on Fin 9 -/

namespace aut9h18a

/-- The 18 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 6, 4, 7, 2, 8, 1, 3, 5], #[1, 0, 3, 2, 5, 4, 7, 6, 8], #[1, 7, 5, 6, 3, 8, 0, 2, 4], #[2, 5, 4, 1, 0, 3, 7, 8, 6], #[2, 7, 0, 8, 4, 6, 5, 1, 3], #[3, 4, 5, 0, 1, 2, 6, 8, 7], #[3, 6, 1, 8, 5, 7, 4, 0, 2], #[4, 3, 0, 5, 2, 1, 8, 6, 7], #[4, 8, 2, 6, 0, 7, 3, 5, 1], #[5, 2, 1, 4, 3, 0, 8, 7, 6], #[5, 8, 3, 7, 1, 6, 2, 4, 0], #[6, 0, 7, 4, 8, 2, 3, 1, 5], #[6, 3, 8, 1, 7, 5, 0, 4, 2], #[7, 1, 6, 5, 8, 3, 2, 0, 4], #[7, 2, 8, 0, 6, 4, 1, 5, 3], #[8, 4, 6, 2, 7, 0, 5, 3, 1], #[8, 5, 7, 3, 6, 1, 4, 2, 0]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 6, 4, 7, 2, 8, 1, 3, 5], #[1, 0, 3, 2, 5, 4, 7, 6, 8], #[6, 0, 7, 4, 8, 2, 3, 1, 5], #[4, 3, 0, 5, 2, 1, 8, 6, 7], #[2, 7, 0, 8, 4, 6, 5, 1, 3], #[3, 4, 5, 0, 1, 2, 6, 8, 7], #[7, 2, 8, 0, 6, 4, 1, 5, 3], #[2, 5, 4, 1, 0, 3, 7, 8, 6], #[4, 8, 2, 6, 0, 7, 3, 5, 1], #[5, 2, 1, 4, 3, 0, 8, 7, 6], #[8, 4, 6, 2, 7, 0, 5, 3, 1], #[1, 7, 5, 6, 3, 8, 0, 2, 4], #[6, 3, 8, 1, 7, 5, 0, 4, 2], #[7, 1, 6, 5, 8, 3, 2, 0, 4], #[3, 6, 1, 8, 5, 7, 4, 0, 2], #[5, 8, 3, 7, 1, 6, 2, 4, 0], #[8, 5, 7, 3, 6, 1, 4, 2, 0]]

def E (i : Fin 18) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 18) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (5 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 5]]

def rep (i : Fin 5) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[2, 1], #[4, 0], #[1, 1], #[3, 1], #[4, 1]], #[#[1, 2], #[0, 2], #[3, 2], #[2, 2], #[4, 2], #[2, 3], #[3, 3], #[1, 3], #[4, 3]], #[#[2, 5], #[3, 4], #[0, 4], #[4, 4], #[2, 4], #[1, 4], #[4, 5], #[1, 5], #[3, 5]], #[#[3, 6], #[2, 7], #[4, 6], #[0, 6], #[1, 6], #[2, 6], #[1, 7], #[4, 7], #[3, 7]], #[#[2, 8], #[4, 8], #[2, 9], #[1, 8], #[0, 8], #[3, 8], #[3, 9], #[4, 9], #[1, 9]], #[#[4, 10], #[2, 10], #[1, 10], #[2, 11], #[3, 10], #[0, 10], #[4, 11], #[3, 11], #[1, 11]], #[#[1, 12], #[3, 13], #[4, 12], #[1, 13], #[3, 12], #[4, 13], #[0, 12], #[2, 12], #[2, 13]], #[#[3, 15], #[1, 14], #[1, 15], #[4, 14], #[4, 15], #[3, 14], #[2, 14], #[0, 14], #[2, 15]], #[#[4, 16], #[4, 17], #[3, 16], #[3, 17], #[1, 16], #[1, 17], #[2, 16], #[2, 17], #[0, 16]]]

def tr (x y : Fin 9) : Fin 5 × Fin 18 := (⟨((trd[x.1]!)[y.1]!)[0]! % 5, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 18, Nat.mod_lt _ (by decide)⟩)

end aut9h18a

namespace aut9h18a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0]

def z (i : Fin 5) : Fin 18 := ⟨zd[i.1]! % 18, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]

def st (i : Fin 5) (j : Fin 18) : Fin 18 := ⟨(std[i.1]!)[j.1]! % 18, Nat.mod_lt _ (by decide)⟩

end aut9h18a

/-! ### The sources -/

/-- A model of equation 167 on `Fin 9` invariant under aut9h18a. -/
def aut9h18aMd167 : Array (Array Nat) := #[#[0, 2, 3, 8, 7, 3, 4, 5, 7], #[3, 1, 8, 2, 2, 6, 4, 5, 6], #[8, 6, 2, 1, 1, 4, 8, 0, 3], #[7, 8, 0, 3, 5, 0, 1, 8, 2], #[5, 5, 6, 0, 4, 7, 1, 6, 2], #[4, 4, 1, 7, 6, 5, 7, 0, 3], #[7, 2, 4, 8, 5, 1, 6, 4, 1], #[3, 6, 8, 5, 0, 4, 5, 7, 0], #[2, 3, 1, 0, 6, 7, 2, 3, 8]]

@[reducible]
def aut9h18aM167 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h18aMd167[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 464 on `Fin 9` invariant under aut9h18a. -/
def aut9h18aMd464 : Array (Array Nat) := #[#[0, 8, 4, 6, 2, 7, 5, 1, 3], #[8, 1, 7, 5, 6, 3, 0, 4, 2], #[4, 7, 2, 8, 0, 6, 1, 3, 5], #[6, 5, 8, 3, 7, 1, 2, 0, 4], #[2, 6, 0, 7, 4, 8, 3, 5, 1], #[7, 3, 6, 1, 8, 5, 4, 2, 0], #[5, 0, 1, 2, 3, 4, 6, 8, 7], #[1, 4, 3, 0, 5, 2, 8, 7, 6], #[3, 2, 5, 4, 1, 0, 7, 6, 8]]

@[reducible]
def aut9h18aM464 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h18aMd464[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 1113 on `Fin 9` invariant under aut9h18a. -/
def aut9h18aMd1113 : Array (Array Nat) := #[#[0, 2, 5, 7, 8, 1, 4, 3, 6], #[3, 1, 6, 4, 0, 8, 2, 5, 7], #[6, 8, 2, 5, 3, 4, 7, 0, 1], #[8, 7, 4, 3, 5, 2, 1, 6, 0], #[1, 3, 7, 0, 4, 6, 5, 8, 2], #[2, 0, 1, 6, 7, 5, 8, 4, 3], #[7, 4, 0, 8, 1, 3, 6, 2, 5], #[5, 6, 8, 1, 2, 0, 3, 7, 4], #[4, 5, 3, 2, 6, 7, 0, 1, 8]]

@[reducible]
def aut9h18aM1113 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h18aMd1113[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 3548 on `Fin 9` invariant under aut9h18a. -/
def aut9h18aMd3548 : Array (Array Nat) := #[#[0, 3, 8, 7, 5, 4, 7, 3, 2], #[2, 1, 6, 8, 5, 4, 2, 6, 3], #[3, 8, 2, 0, 6, 1, 4, 8, 1], #[8, 2, 1, 3, 0, 7, 8, 5, 0], #[7, 2, 1, 5, 4, 6, 5, 0, 6], #[3, 6, 4, 0, 7, 5, 1, 4, 7], #[4, 4, 8, 1, 1, 7, 6, 5, 2], #[5, 5, 0, 8, 6, 0, 4, 7, 3], #[7, 6, 3, 2, 2, 3, 1, 0, 8]]

@[reducible]
def aut9h18aM3548 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h18aMd3548[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
