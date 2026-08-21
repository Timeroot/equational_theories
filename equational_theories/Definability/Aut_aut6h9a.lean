import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 9 on Fin 6

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 26244 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 9 on Fin 6 -/

namespace aut6h9a

/-- The 9 permutations of `Fin 6`, and their inverses. -/
def E : Fin 9 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 4, 5, 3], ![0, 1, 2, 5, 3, 4], ![1, 2, 0, 3, 4, 5], ![1, 2, 0, 4, 5, 3], ![1, 2, 0, 5, 3, 4], ![2, 0, 1, 3, 4, 5], ![2, 0, 1, 4, 5, 3], ![2, 0, 1, 5, 3, 4]]

def Einv : Fin 9 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 5, 3, 4], ![0, 1, 2, 4, 5, 3], ![2, 0, 1, 3, 4, 5], ![2, 0, 1, 5, 3, 4], ![2, 0, 1, 4, 5, 3], ![1, 2, 0, 3, 4, 5], ![1, 2, 0, 5, 3, 4], ![1, 2, 0, 4, 5, 3]]

/-- One ordered pair per orbit (8 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 8 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (3, 0), (3, 3), (3, 4), (3, 5)]

def tr : Fin 6 → Fin 6 → Fin 8 × Fin 9 := fun x y ↦
  ![![(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (3, 2)], ![(2, 3), (0, 3), (1, 3), (3, 3), (3, 4), (3, 5)], ![(1, 6), (2, 6), (0, 6), (3, 6), (3, 7), (3, 8)], ![(4, 0), (4, 3), (4, 6), (5, 0), (6, 0), (7, 0)], ![(4, 1), (4, 4), (4, 7), (7, 1), (5, 1), (6, 1)], ![(4, 2), (4, 5), (4, 8), (6, 2), (7, 2), (5, 2)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h9a

namespace aut6h9a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 8 → Fin 9 := ![0, 0, 0, 0, 0, 0, 0, 0]

def st : Fin 8 → Fin 9 → Fin 9 := fun i j ↦
  ![![0, 0, 0, 3, 3, 3, 6, 6, 6], ![0, 0, 0, 3, 3, 3, 6, 6, 6], ![0, 0, 0, 3, 3, 3, 6, 6, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 1, 2, 0, 1, 2, 0, 1, 2], ![0, 1, 2, 0, 1, 2, 0, 1, 2], ![0, 1, 2, 0, 1, 2, 0, 1, 2]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h9a

/-! ### The sources -/

/-- A model of equation 3355 on `Fin 6` invariant under aut6h9a. -/
@[reducible]
def aut6h9aM3355 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![0, 0, 2, 0, 0, 0], ![0, 1, 1, 1, 1, 1], ![2, 1, 2, 2, 2, 2], ![0, 1, 2, 3, 3, 5], ![0, 1, 2, 3, 4, 4], ![0, 1, 2, 5, 4, 5]] x y

theorem aut6h9aM3355_models : @satisfies _ (Fin 6) aut6h9aM3355 Law3355 :=
  (@Law3355.models_iff (Fin 6) aut6h9aM3355).mpr (by native_decide)

theorem aut6h9aM3355_endo : ∀ i, aut6h9aM3355.IsEndo (aut6h9a.E i) := by decide
