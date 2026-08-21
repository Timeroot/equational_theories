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
def E : Fin 6 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![1, 2, 0, 4, 5, 3], ![2, 0, 1, 5, 3, 4], ![3, 4, 5, 1, 2, 0], ![4, 5, 3, 2, 0, 1], ![5, 3, 4, 0, 1, 2]]

def Einv : Fin 6 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![2, 0, 1, 5, 3, 4], ![1, 2, 0, 4, 5, 3], ![5, 3, 4, 0, 1, 2], ![4, 5, 3, 2, 0, 1], ![3, 4, 5, 1, 2, 0]]

/-- One ordered pair per orbit (6 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 6 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]

def tr : Fin 6 → Fin 6 → Fin 6 × Fin 6 := fun x y ↦
  ![![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)], ![(2, 1), (0, 1), (1, 1), (5, 1), (3, 1), (4, 1)], ![(1, 2), (2, 2), (0, 2), (4, 2), (5, 2), (3, 2)], ![(5, 3), (3, 3), (4, 3), (0, 3), (1, 3), (2, 3)], ![(4, 4), (5, 4), (3, 4), (2, 4), (0, 4), (1, 4)], ![(3, 5), (4, 5), (5, 5), (1, 5), (2, 5), (0, 5)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h6b

namespace aut6h6b

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 6 → Fin 6 := ![0, 0, 0, 0, 0, 0]

def st : Fin 6 → Fin 6 → Fin 6 := fun i j ↦
  ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h6b

/-! ### The sources -/

/-- A model of equation 3558 on `Fin 6` invariant under aut6h6b. -/
@[reducible]
def aut6h6bM3558 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![3, 0, 2, 0, 4, 5], ![0, 4, 1, 3, 1, 5], ![2, 1, 5, 3, 4, 2], ![0, 3, 2, 1, 3, 5], ![0, 1, 4, 3, 2, 4], ![5, 1, 2, 5, 4, 0]] x y

theorem aut6h6bM3558_models : @satisfies _ (Fin 6) aut6h6bM3558 Law3558 :=
  (@Law3558.models_iff (Fin 6) aut6h6bM3558).mpr (by native_decide)

theorem aut6h6bM3558_endo : ∀ i, aut6h6bM3558.IsEndo (aut6h6b.E i) := by decide

/-- A model of equation 4405 on `Fin 6` invariant under aut6h6b. -/
@[reducible]
def aut6h6bM4405 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![0, 0, 2, 3, 1, 0], ![0, 1, 1, 1, 4, 2], ![2, 1, 2, 0, 2, 5], ![3, 1, 4, 3, 3, 5], ![5, 4, 2, 3, 4, 4], ![0, 3, 5, 5, 4, 5]] x y

theorem aut6h6bM4405_models : @satisfies _ (Fin 6) aut6h6bM4405 Law4405 :=
  (@Law4405.models_iff (Fin 6) aut6h6bM4405).mpr (by native_decide)

theorem aut6h6bM4405_endo : ∀ i, aut6h6bM4405.IsEndo (aut6h6b.E i) := by decide

/-- A model of equation 4443 on `Fin 6` invariant under aut6h6b. -/
@[reducible]
def aut6h6bM4443 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![0, 0, 2, 3, 2, 0], ![0, 1, 1, 1, 4, 0], ![2, 1, 2, 1, 2, 5], ![3, 1, 5, 3, 3, 5], ![3, 4, 2, 3, 4, 4], ![0, 4, 5, 5, 4, 5]] x y

theorem aut6h6bM4443_models : @satisfies _ (Fin 6) aut6h6bM4443 Law4443 :=
  (@Law4443.models_iff (Fin 6) aut6h6bM4443).mpr (by native_decide)

theorem aut6h6bM4443_endo : ∀ i, aut6h6bM4443.IsEndo (aut6h6b.E i) := by decide
