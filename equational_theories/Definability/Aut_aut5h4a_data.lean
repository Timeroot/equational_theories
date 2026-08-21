import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 4 on Fin 5

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 15625 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 4 on Fin 5 -/

namespace aut5h4a

/-- The 4 permutations of `Fin 5`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4], #[1, 3, 0, 2, 4], #[2, 0, 3, 1, 4], #[3, 2, 1, 0, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4], #[2, 0, 3, 1, 4], #[1, 3, 0, 2, 4], #[3, 2, 1, 0, 4]]

def E (i : Fin 4) (x : Fin 5) : Fin 5 := ⟨(Ed[i.1]!)[x.1]! % 5, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 4) (x : Fin 5) : Fin 5 := ⟨(Eid[i.1]!)[x.1]! % 5, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (7 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[4, 0], #[4, 4]]

def rep (i : Fin 7) : Fin 5 × Fin 5 := (⟨(repd[i.1]!)[0]! % 5, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 5, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0]], #[#[2, 1], #[0, 1], #[3, 1], #[1, 1], #[4, 1]], #[#[1, 2], #[3, 2], #[0, 2], #[2, 2], #[4, 2]], #[#[3, 3], #[2, 3], #[1, 3], #[0, 3], #[4, 3]], #[#[5, 0], #[5, 1], #[5, 2], #[5, 3], #[6, 0]]]

def tr (x y : Fin 5) : Fin 7 × Fin 4 := (⟨((trd[x.1]!)[y.1]!)[0]! % 7, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 4, Nat.mod_lt _ (by decide)⟩)

end aut5h4a

namespace aut5h4a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 7) : Fin 4 := ⟨zd[i.1]! % 4, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 1, 2, 3], #[0, 0, 0, 0]]

def st (i : Fin 7) (j : Fin 4) : Fin 4 := ⟨(std[i.1]!)[j.1]! % 4, Nat.mod_lt _ (by decide)⟩

end aut5h4a

/-! ### The sources -/

/-- A model of equation 115 on `Fin 5` invariant under aut5h4a. -/
def aut5h4aMd115 : Array (Array Nat) := #[#[1, 2, 4, 3, 0], #[4, 3, 2, 0, 1], #[3, 1, 0, 4, 2], #[0, 4, 1, 2, 3], #[2, 0, 3, 1, 4]]

@[reducible]
def aut5h4aM115 : Magma (Fin 5) := Magma.mk fun x y ↦ ⟨(aut5h4aMd115[x.1]!)[y.1]! % 5, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 481 on `Fin 5` invariant under aut5h4a. -/
def aut5h4aMd481 : Array (Array Nat) := #[#[4, 0, 1, 3, 2], #[3, 4, 2, 1, 0], #[2, 1, 4, 0, 3], #[0, 2, 3, 4, 1], #[1, 3, 0, 2, 4]]

@[reducible]
def aut5h4aM481 : Magma (Fin 5) := Magma.mk fun x y ↦ ⟨(aut5h4aMd481[x.1]!)[y.1]! % 5, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 501 on `Fin 5` invariant under aut5h4a. -/
def aut5h4aMd501 : Array (Array Nat) := #[#[3, 1, 4, 2, 0], #[4, 2, 0, 3, 1], #[0, 3, 1, 4, 2], #[1, 4, 2, 0, 3], #[1, 3, 0, 2, 4]]

@[reducible]
def aut5h4aM501 : Magma (Fin 5) := Magma.mk fun x y ↦ ⟨(aut5h4aMd501[x.1]!)[y.1]! % 5, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 873 on `Fin 5` invariant under aut5h4a. -/
def aut5h4aMd873 : Array (Array Nat) := #[#[1, 4, 3, 0, 2], #[2, 3, 1, 4, 0], #[4, 2, 0, 1, 3], #[3, 0, 4, 2, 1], #[0, 1, 2, 3, 4]]

@[reducible]
def aut5h4aM873 : Magma (Fin 5) := Magma.mk fun x y ↦ ⟨(aut5h4aMd873[x.1]!)[y.1]! % 5, Nat.mod_lt _ (by decide)⟩
