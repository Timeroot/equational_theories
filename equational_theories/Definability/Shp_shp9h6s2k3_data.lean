import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: shape 2 shuffle on Fin 9

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 2541865828329 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000
-- an array literal is elaborated by recursion on its own length, and `AGL(1, 31)` is 930 rows
set_option maxRecDepth 4000000

open Law Law.MagmaLaw

/-! ### shape 2 shuffle on Fin 9 -/

namespace shp9h6s2k3

/-- The 6 permutations of `Fin 3`, and their inverses. Permutation `i`
of `Fin 9` acts on each part (2,) of the carrier by moving every base-`3`
digit of that part, which is what makes `Sym(S)` a group of automorphisms of every
invariant operation. -/
def Sd : Array (Array Nat) := #[#[0, 1, 2], #[0, 2, 1], #[1, 0, 2], #[1, 2, 0], #[2, 0, 1], #[2, 1, 0]]

def Sid : Array (Array Nat) := #[#[0, 1, 2], #[0, 2, 1], #[1, 0, 2], #[2, 0, 1], #[1, 2, 0], #[2, 1, 0]]

def E (i : Fin 6) (x : Fin 9) : Fin 9 := ⟨((Sd[i.1]!)[x.1 / 3 % 3]! * 3 + (Sd[i.1]!)[x.1 % 3]!) % 9, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 6) (x : Fin 9) : Fin 9 := ⟨((Sid[i.1]!)[x.1 / 3 % 3]! * 3 + (Sid[i.1]!)[x.1 % 3]!) % 9, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (14 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 3], #[0, 4], #[0, 5], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

def rep (i : Fin 14) : Fin 9 × Fin 9 := (⟨(repd[i.1]!)[0]! % 9, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 9, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[1, 1], #[2, 0], #[3, 0], #[4, 0], #[2, 1], #[4, 1], #[3, 1]], #[#[5, 0], #[6, 0], #[7, 0], #[8, 0], #[9, 0], #[10, 0], #[11, 0], #[12, 0], #[13, 0]], #[#[5, 1], #[7, 1], #[6, 1], #[11, 1], #[13, 1], #[12, 1], #[8, 1], #[10, 1], #[9, 1]], #[#[9, 2], #[8, 2], #[10, 2], #[6, 2], #[5, 2], #[7, 2], #[12, 2], #[11, 2], #[13, 2]], #[#[3, 2], #[2, 2], #[4, 2], #[1, 2], #[0, 2], #[1, 3], #[4, 3], #[2, 3], #[3, 3]], #[#[13, 3], #[11, 3], #[12, 3], #[7, 3], #[5, 3], #[6, 3], #[10, 3], #[8, 3], #[9, 3]], #[#[9, 4], #[10, 4], #[8, 4], #[12, 4], #[13, 4], #[11, 4], #[6, 4], #[7, 4], #[5, 4]], #[#[13, 5], #[12, 5], #[11, 5], #[10, 5], #[9, 5], #[8, 5], #[7, 5], #[6, 5], #[5, 5]], #[#[3, 4], #[4, 4], #[2, 4], #[4, 5], #[3, 5], #[2, 5], #[1, 4], #[1, 5], #[0, 4]]]

def tr (x y : Fin 9) : Fin 14 × Fin 6 := (⟨((trd[x.1]!)[y.1]!)[0]! % 14, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

end shp9h6s2k3

namespace shp9h6s2k3

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def z (i : Fin 14) : Fin 6 := ⟨zd[i.1]! % 6, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 0, 2, 2, 4, 4], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5]]

def st (i : Fin 14) (j : Fin 6) : Fin 6 := ⟨(std[i.1]!)[j.1]! % 6, Nat.mod_lt _ (by decide)⟩

end shp9h6s2k3

/-! ### The sources -/

/-- A model of equation 667 on `Fin 9` invariant under shp9h6s2k3. -/
def shp9h6s2k3Md667 : Array (Array Nat) := #[#[0, 4, 8, 2, 5, 3, 1, 6, 7], #[3, 7, 2, 1, 6, 0, 5, 8, 4], #[6, 1, 5, 7, 8, 4, 2, 0, 3], #[7, 3, 4, 6, 1, 5, 8, 2, 0], #[2, 5, 1, 0, 4, 8, 7, 3, 6], #[8, 6, 0, 3, 7, 2, 4, 5, 1], #[5, 8, 6, 4, 0, 1, 3, 7, 2], #[4, 0, 3, 8, 2, 7, 6, 1, 5], #[1, 2, 7, 5, 3, 6, 0, 4, 8]]

@[reducible]
def shp9h6s2k3M667 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(shp9h6s2k3Md667[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 3279 on `Fin 9` invariant under shp9h6s2k3. -/
def shp9h6s2k3Md3279 : Array (Array Nat) := #[#[0, 4, 8, 1, 1, 1, 2, 2, 2], #[8, 8, 6, 7, 6, 7, 0, 4, 8], #[4, 3, 4, 0, 4, 8, 5, 5, 3], #[7, 6, 6, 8, 8, 7, 0, 4, 8], #[3, 3, 3, 0, 4, 8, 5, 5, 5], #[0, 4, 8, 1, 0, 0, 2, 2, 1], #[5, 3, 3, 0, 4, 8, 4, 5, 4], #[0, 4, 8, 1, 2, 1, 2, 0, 0], #[6, 6, 6, 7, 7, 7, 0, 4, 8]]

@[reducible]
def shp9h6s2k3M3279 : Magma (Fin 9) := Magma.mk fun x y ↦ ⟨(shp9h6s2k3Md3279[x.1]!)[y.1]! % 9, Nat.mod_lt _ (by decide)⟩
