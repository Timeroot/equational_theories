import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 6 on Fin 6 (#2)

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 46656 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 6 on Fin 6 (#2) -/

namespace aut6h6b

/-- The 6 permutations of `Fin 6`, and their inverses. -/
def Ed : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[1, 2, 0, 4, 5, 3], #[2, 0, 1, 5, 3, 4], #[3, 4, 5, 1, 2, 0], #[4, 5, 3, 2, 0, 1], #[5, 3, 4, 0, 1, 2]]

def Eid : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[2, 0, 1, 5, 3, 4], #[1, 2, 0, 4, 5, 3], #[5, 3, 4, 0, 1, 2], #[4, 5, 3, 2, 0, 1], #[3, 4, 5, 1, 2, 0]]

def E (i : Fin 6) (x : Fin 6) : Fin 6 := ⟨(Ed[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

def Einv (i : Fin 6) (x : Fin 6) : Fin 6 := ⟨(Eid[i.1]!)[x.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- One ordered pair per orbit (6 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def repd : Array (Array Nat) := #[#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5]]

def rep (i : Fin 6) : Fin 6 × Fin 6 := (⟨(repd[i.1]!)[0]! % 6, Nat.mod_lt _ (by decide)⟩, ⟨(repd[i.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

def trd : Array (Array (Array Nat)) := #[#[#[0, 0], #[1, 0], #[2, 0], #[3, 0], #[4, 0], #[5, 0]], #[#[2, 1], #[0, 1], #[1, 1], #[5, 1], #[3, 1], #[4, 1]], #[#[1, 2], #[2, 2], #[0, 2], #[4, 2], #[5, 2], #[3, 2]], #[#[5, 3], #[3, 3], #[4, 3], #[0, 3], #[1, 3], #[2, 3]], #[#[4, 4], #[5, 4], #[3, 4], #[2, 4], #[0, 4], #[1, 4]], #[#[3, 5], #[4, 5], #[5, 5], #[1, 5], #[2, 5], #[0, 5]]]

def tr (x y : Fin 6) : Fin 6 × Fin 6 := (⟨((trd[x.1]!)[y.1]!)[0]! % 6, Nat.mod_lt _ (by decide)⟩, ⟨((trd[x.1]!)[y.1]!)[1]! % 6, Nat.mod_lt _ (by decide)⟩)

end aut6h6b

namespace aut6h6b

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def zd : Array Nat := #[0, 0, 0, 0, 0, 0]

def z (i : Fin 6) : Fin 6 := ⟨zd[i.1]! % 6, Nat.mod_lt _ (by decide)⟩

def std : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5]]

def st (i : Fin 6) (j : Fin 6) : Fin 6 := ⟨(std[i.1]!)[j.1]! % 6, Nat.mod_lt _ (by decide)⟩

end aut6h6b

/-! ### The sources -/

/-- A model of equation 3558 on `Fin 6` invariant under aut6h6b. -/
def aut6h6bMd3558 : Array (Array Nat) := #[#[3, 0, 2, 0, 4, 5], #[0, 4, 1, 3, 1, 5], #[2, 1, 5, 3, 4, 2], #[0, 3, 2, 1, 3, 5], #[0, 1, 4, 3, 2, 4], #[5, 1, 2, 5, 4, 0]]

@[reducible]
def aut6h6bM3558 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(aut6h6bMd3558[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 4405 on `Fin 6` invariant under aut6h6b. -/
def aut6h6bMd4405 : Array (Array Nat) := #[#[0, 0, 2, 3, 1, 0], #[0, 1, 1, 1, 4, 2], #[2, 1, 2, 0, 2, 5], #[3, 1, 4, 3, 3, 5], #[5, 4, 2, 3, 4, 4], #[0, 3, 5, 5, 4, 5]]

@[reducible]
def aut6h6bM4405 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(aut6h6bMd4405[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩

/-- A model of equation 4443 on `Fin 6` invariant under aut6h6b. -/
def aut6h6bMd4443 : Array (Array Nat) := #[#[0, 0, 2, 3, 2, 0], #[0, 1, 1, 1, 4, 0], #[2, 1, 2, 1, 2, 5], #[3, 1, 5, 3, 3, 5], #[3, 4, 2, 3, 4, 4], #[0, 4, 5, 5, 4, 5]]

@[reducible]
def aut6h6bM4443 : Magma (Fin 6) := Magma.mk fun x y ↦ ⟨(aut6h6bMd4443[x.1]!)[y.1]! % 6, Nat.mod_lt _ (by decide)⟩
