import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 8 on Fin 5

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 405 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 8 on Fin 5 -/

namespace aut5h8a

/-- The 8 permutations of `Fin 5`, and their inverses. -/
def E : Fin 8 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3], ![0, 3, 4, 1, 2], ![0, 3, 4, 2, 1], ![0, 4, 3, 1, 2], ![0, 4, 3, 2, 1]]

def Einv : Fin 8 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3], ![0, 3, 4, 1, 2], ![0, 4, 3, 1, 2], ![0, 3, 4, 2, 1], ![0, 4, 3, 2, 1]]

/-- One ordered pair per orbit (6 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 6 → Fin 5 × Fin 5 := ![(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3)]

def tr : Fin 5 → Fin 5 → Fin 6 × Fin 8 := fun x y ↦
  ![![(0, 0), (1, 0), (1, 2), (1, 4), (1, 6)], ![(2, 0), (3, 0), (4, 0), (5, 0), (5, 1)], ![(2, 2), (4, 2), (3, 2), (5, 2), (5, 3)], ![(2, 4), (5, 4), (5, 5), (3, 4), (4, 4)], ![(2, 6), (5, 6), (5, 7), (4, 6), (3, 6)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut5h8a

namespace aut5h8a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 6 → Fin 8 := ![0, 0, 0, 0, 0, 0]

def st : Fin 6 → Fin 8 → Fin 8 := fun i j ↦
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 2, 4, 4, 6, 6], ![0, 0, 2, 2, 4, 4, 6, 6], ![0, 0, 2, 2, 4, 4, 6, 6], ![0, 0, 2, 2, 4, 4, 6, 6], ![0, 1, 2, 3, 4, 5, 6, 7]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut5h8a

/-! ### The sources -/

/-- A model of equation 474 on `Fin 5` invariant under aut5h8a. -/
@[reducible]
def aut5h8aM474 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 2, 1, 4, 3], ![1, 0, 2, 3, 4], ![2, 1, 0, 3, 4], ![3, 1, 2, 0, 4], ![4, 1, 2, 3, 0]] x y

theorem aut5h8aM474_models : @satisfies _ (Fin 5) aut5h8aM474 Law474 :=
  (@Law474.models_iff (Fin 5) aut5h8aM474).mpr (by native_decide)

theorem aut5h8aM474_endo : ∀ i, aut5h8aM474.IsEndo (aut5h8a.E i) := by decide

/-- A model of equation 1685 on `Fin 5` invariant under aut5h8a. -/
@[reducible]
def aut5h8aM1685 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 2, 1, 4, 3], ![1, 0, 2, 3, 4], ![2, 1, 0, 3, 4], ![3, 1, 2, 0, 4], ![4, 1, 2, 3, 0]] x y

theorem aut5h8aM1685_models : @satisfies _ (Fin 5) aut5h8aM1685 Law1685 :=
  (@Law1685.models_iff (Fin 5) aut5h8aM1685).mpr (by native_decide)

theorem aut5h8aM1685_endo : ∀ i, aut5h8aM1685.IsEndo (aut5h8a.E i) := by decide
