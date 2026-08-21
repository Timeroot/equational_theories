import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 110 on Fin 11

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 11 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### group of order 110 on Fin 11 -/

namespace aff11h110a

/-- The 10 units the group uses, and their inverses: permutation `u * 11 + v` is `x ↦ u x + v`. -/
def Ud : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def Uid : Array Nat := #[1, 6, 4, 3, 9, 2, 8, 7, 5, 10]

def E (i : Fin 110) (x : Fin 11) : Fin 11 := ⟨(Ud[i.1 / 11]! * x.1 + i.1 % 11) % 11, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 110) (x : Fin 11) : Fin 11 := ⟨Uid[i.1 / 11]! * ((x.1 + 11 - i.1 % 11) % 11) % 11, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (2 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1]]

def rep (i : Fin 2) : Fin 11 × Fin 11 := (⟨(repd[i.1]!)[0]! % 11, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 11, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[1, 11], #[1, 22], #[1, 33], #[1, 44], #[1, 55], #[1, 66], #[1, 77], #[1, 88], #[1, 99]], #[#[1, 100], #[0, 1], #[1, 1], #[1, 12], #[1, 23], #[1, 34], #[1, 45], #[1, 56], #[1, 67], #[1, 78], #[1, 89]], #[#[1, 90], #[1, 101], #[0, 2], #[1, 2], #[1, 13], #[1, 24], #[1, 35], #[1, 46], #[1, 57], #[1, 68], #[1, 79]], #[#[1, 80], #[1, 91], #[1, 102], #[0, 3], #[1, 3], #[1, 14], #[1, 25], #[1, 36], #[1, 47], #[1, 58], #[1, 69]], #[#[1, 70], #[1, 81], #[1, 92], #[1, 103], #[0, 4], #[1, 4], #[1, 15], #[1, 26], #[1, 37], #[1, 48], #[1, 59]], #[#[1, 60], #[1, 71], #[1, 82], #[1, 93], #[1, 104], #[0, 5], #[1, 5], #[1, 16], #[1, 27], #[1, 38], #[1, 49]], #[#[1, 50], #[1, 61], #[1, 72], #[1, 83], #[1, 94], #[1, 105], #[0, 6], #[1, 6], #[1, 17], #[1, 28], #[1, 39]], #[#[1, 40], #[1, 51], #[1, 62], #[1, 73], #[1, 84], #[1, 95], #[1, 106], #[0, 7], #[1, 7], #[1, 18], #[1, 29]], #[#[1, 30], #[1, 41], #[1, 52], #[1, 63], #[1, 74], #[1, 85], #[1, 96], #[1, 107], #[0, 8], #[1, 8], #[1, 19]], #[#[1, 20], #[1, 31], #[1, 42], #[1, 53], #[1, 64], #[1, 75], #[1, 86], #[1, 97], #[1, 108], #[0, 9], #[1, 9]], #[#[1, 10], #[1, 21], #[1, 32], #[1, 43], #[1, 54], #[1, 65], #[1, 76], #[1, 87], #[1, 98], #[1, 109], #[0, 10]]]

def tr (x y : Fin 11) : Fin 2 × Fin 110 := (⟨((trd[x.1]!)[y.1]!)[0]! % 2, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 110, Nat.mod_lt _ (by decide)⟩)

end aff11h110a

namespace aff11h110a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0]

def z (i : Fin 2) : Fin 110 := ⟨zd[i.1]! % 110, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]]

def st (i : Fin 2) (j : Fin 110) : Fin 110 := ⟨(std[i.1]!)[j.1]! % 110, Nat.mod_lt _ (by decide)⟩

end aff11h110a

/-! ### The sources -/

/-- A model of equation 474 on `Fin 11` invariant under aff11h110a. -/
def aff11h110aMd474 : Array (Array Nat) := #[#[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9], #[10, 1, 3, 5, 7, 9, 0, 2, 4, 6, 8], #[9, 0, 2, 4, 6, 8, 10, 1, 3, 5, 7], #[8, 10, 1, 3, 5, 7, 9, 0, 2, 4, 6], #[7, 9, 0, 2, 4, 6, 8, 10, 1, 3, 5], #[6, 8, 10, 1, 3, 5, 7, 9, 0, 2, 4], #[5, 7, 9, 0, 2, 4, 6, 8, 10, 1, 3], #[4, 6, 8, 10, 1, 3, 5, 7, 9, 0, 2], #[3, 5, 7, 9, 0, 2, 4, 6, 8, 10, 1], #[2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 0], #[1, 3, 5, 7, 9, 0, 2, 4, 6, 8, 10]]

@[reducible]
def aff11h110aM474 : Magma (Fin 11) := Magma.mk fun x y ↦ ⟨(aff11h110aMd474[x.1]!)[y.1]! % 11, Nat.mod_lt _ (by decide)⟩
