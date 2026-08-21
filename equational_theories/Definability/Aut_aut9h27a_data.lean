import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 27 on Fin 9

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 2187 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 27 on Fin 9 -/

namespace aut9h27a

/-- The 27 permutations of `Fin 9`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 4, 5, 3, 7, 8, 6], #[0, 1, 2, 5, 3, 4, 8, 6, 7], #[1, 2, 0, 3, 4, 5, 8, 6, 7], #[1, 2, 0, 4, 5, 3, 6, 7, 8], #[1, 2, 0, 5, 3, 4, 7, 8, 6], #[2, 0, 1, 3, 4, 5, 7, 8, 6], #[2, 0, 1, 4, 5, 3, 8, 6, 7], #[2, 0, 1, 5, 3, 4, 6, 7, 8], #[3, 5, 4, 6, 8, 7, 2, 0, 1], #[3, 5, 4, 7, 6, 8, 1, 2, 0], #[3, 5, 4, 8, 7, 6, 0, 1, 2], #[4, 3, 5, 6, 8, 7, 0, 1, 2], #[4, 3, 5, 7, 6, 8, 2, 0, 1], #[4, 3, 5, 8, 7, 6, 1, 2, 0], #[5, 4, 3, 6, 8, 7, 1, 2, 0], #[5, 4, 3, 7, 6, 8, 0, 1, 2], #[5, 4, 3, 8, 7, 6, 2, 0, 1], #[6, 7, 8, 0, 2, 1, 5, 4, 3], #[6, 7, 8, 1, 0, 2, 3, 5, 4], #[6, 7, 8, 2, 1, 0, 4, 3, 5], #[7, 8, 6, 0, 2, 1, 3, 5, 4], #[7, 8, 6, 1, 0, 2, 4, 3, 5], #[7, 8, 6, 2, 1, 0, 5, 4, 3], #[8, 6, 7, 0, 2, 1, 4, 3, 5], #[8, 6, 7, 1, 0, 2, 5, 4, 3], #[8, 6, 7, 2, 1, 0, 3, 5, 4]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8], #[0, 1, 2, 5, 3, 4, 8, 6, 7], #[0, 1, 2, 4, 5, 3, 7, 8, 6], #[2, 0, 1, 3, 4, 5, 7, 8, 6], #[2, 0, 1, 5, 3, 4, 6, 7, 8], #[2, 0, 1, 4, 5, 3, 8, 6, 7], #[1, 2, 0, 3, 4, 5, 8, 6, 7], #[1, 2, 0, 5, 3, 4, 7, 8, 6], #[1, 2, 0, 4, 5, 3, 6, 7, 8], #[7, 8, 6, 0, 2, 1, 3, 5, 4], #[8, 6, 7, 0, 2, 1, 4, 3, 5], #[6, 7, 8, 0, 2, 1, 5, 4, 3], #[6, 7, 8, 1, 0, 2, 3, 5, 4], #[7, 8, 6, 1, 0, 2, 4, 3, 5], #[8, 6, 7, 1, 0, 2, 5, 4, 3], #[8, 6, 7, 2, 1, 0, 3, 5, 4], #[6, 7, 8, 2, 1, 0, 4, 3, 5], #[7, 8, 6, 2, 1, 0, 5, 4, 3], #[3, 5, 4, 8, 7, 6, 0, 1, 2], #[4, 3, 5, 6, 8, 7, 0, 1, 2], #[5, 4, 3, 7, 6, 8, 0, 1, 2], #[3, 5, 4, 6, 8, 7, 2, 0, 1], #[4, 3, 5, 7, 6, 8, 2, 0, 1], #[5, 4, 3, 8, 7, 6, 2, 0, 1], #[3, 5, 4, 7, 6, 8, 1, 2, 0], #[4, 3, 5, 8, 7, 6, 1, 2, 0], #[5, 4, 3, 6, 8, 7, 1, 2, 0]]

def E (i : Fin 27) (x : Fin 9) : Fin 9 := ⟨(Ed[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 27) (x : Fin 9) : Fin 9 := ⟨(Eid[i.1]!)[x.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (5 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 6]]

def rep (i : Fin 5) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[3, 1], #[3, 2], #[4, 0], #[4, 1], #[4, 2]], #[#[2, 3], #[0, 3], #[1, 3], #[3, 3], #[3, 4], #[3, 5], #[4, 4], #[4, 5], #[4, 3]], #[#[1, 6], #[2, 6], #[0, 6], #[3, 6], #[3, 7], #[3, 8], #[4, 8], #[4, 6], #[4, 7]], #[#[4, 11], #[4, 10], #[4, 9], #[0, 9], #[2, 9], #[1, 9], #[3, 9], #[3, 10], #[3, 11]], #[#[4, 12], #[4, 14], #[4, 13], #[1, 12], #[0, 12], #[2, 12], #[3, 12], #[3, 13], #[3, 14]], #[#[4, 16], #[4, 15], #[4, 17], #[2, 15], #[1, 15], #[0, 15], #[3, 15], #[3, 16], #[3, 17]], #[#[3, 18], #[3, 19], #[3, 20], #[4, 19], #[4, 20], #[4, 18], #[0, 18], #[1, 18], #[2, 18]], #[#[3, 21], #[3, 22], #[3, 23], #[4, 21], #[4, 22], #[4, 23], #[2, 21], #[0, 21], #[1, 21]], #[#[3, 24], #[3, 25], #[3, 26], #[4, 26], #[4, 24], #[4, 25], #[1, 24], #[2, 24], #[0, 24]]]

def tr (x y : Fin 9) : Fin 5 × Fin 27 := (⟨((trd[x.1]!)[y.1]!)[0]! % 5, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 27, Nat.mod_lt _ (by decide)⟩)

end aut9h27a

namespace aut9h27a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0]

def z (i : Fin 5) : Fin 27 := ⟨zd[i.1]! % 27, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 0, 3, 3, 3, 6, 6, 6, 9, 9, 9, 12, 12, 12, 15, 15, 15, 18, 18, 18, 21, 21, 21, 24, 24, 24], #[0, 0, 0, 3, 3, 3, 6, 6, 6, 9, 9, 9, 12, 12, 12, 15, 15, 15, 18, 18, 18, 21, 21, 21, 24, 24, 24], #[0, 0, 0, 3, 3, 3, 6, 6, 6, 9, 9, 9, 12, 12, 12, 15, 15, 15, 18, 18, 18, 21, 21, 21, 24, 24, 24], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]

def st (i : Fin 5) (j : Fin 27) : Fin 27 := ⟨(std[i.1]!)[j.1]! % 27, Nat.mod_lt _ (by decide)⟩

end aut9h27a

/-! ### The sources -/

/-- A model of equation 464 on `Fin 9` invariant under aut9h27a. -/
def aut9h27aMd464 : Array (Array Nat) := #[#[0, 2, 1, 6, 7, 8, 5, 3, 4], #[2, 1, 0, 8, 6, 7, 3, 4, 5], #[1, 0, 2, 7, 8, 6, 4, 5, 3], #[6, 8, 7, 3, 5, 4, 2, 1, 0], #[7, 6, 8, 5, 4, 3, 0, 2, 1], #[8, 7, 6, 4, 3, 5, 1, 0, 2], #[5, 3, 4, 2, 0, 1, 6, 8, 7], #[3, 4, 5, 1, 2, 0, 8, 7, 6], #[4, 5, 3, 0, 1, 2, 7, 6, 8]]

@[reducible]
def aut9h27aM464 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(aut9h27aMd464[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
