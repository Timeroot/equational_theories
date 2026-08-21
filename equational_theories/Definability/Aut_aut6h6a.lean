import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 6 on Fin 6

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 20736 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 6 on Fin 6 -/

namespace aut6h6a

/-- The 6 permutations of `Fin 6`, and their inverses. -/
def E : Fin 6 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 3, 2, 1, 5, 4], ![1, 0, 4, 3, 2, 5], ![1, 3, 4, 0, 5, 2], ![3, 0, 5, 1, 2, 4], ![3, 1, 5, 0, 4, 2]]

def Einv : Fin 6 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 3, 2, 1, 5, 4], ![1, 0, 4, 3, 2, 5], ![3, 0, 5, 1, 2, 4], ![1, 3, 4, 0, 5, 2], ![3, 1, 5, 0, 4, 2]]

/-- One ordered pair per orbit (8 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 8 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 4), (2, 0), (2, 1), (2, 2), (2, 4)]

def tr : Fin 6 → Fin 6 → Fin 8 × Fin 6 := fun x y ↦
  ![![(0, 0), (1, 0), (2, 0), (1, 1), (3, 0), (3, 1)], ![(1, 2), (0, 2), (3, 2), (1, 3), (2, 2), (3, 3)], ![(4, 0), (5, 0), (6, 0), (5, 1), (7, 0), (7, 1)], ![(1, 4), (1, 5), (3, 4), (0, 4), (3, 5), (2, 4)], ![(5, 2), (4, 2), (7, 2), (5, 3), (6, 2), (7, 3)], ![(5, 4), (5, 5), (7, 4), (4, 4), (7, 5), (6, 4)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut6h6a

namespace aut6h6a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 8 → Fin 6 := ![0, 0, 0, 0, 0, 0, 0, 0]

def st : Fin 8 → Fin 6 → Fin 6 := fun i j ↦
  ![![0, 0, 2, 2, 4, 4], ![0, 1, 2, 3, 4, 5], ![0, 0, 2, 2, 4, 4], ![0, 1, 2, 3, 4, 5], ![0, 0, 2, 2, 4, 4], ![0, 1, 2, 3, 4, 5], ![0, 0, 2, 2, 4, 4], ![0, 1, 2, 3, 4, 5]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut6h6a

/-! ### The sources -/

/-- A model of equation 1482 on `Fin 6` invariant under aut6h6a. -/
@[reducible]
def aut6h6aM1482 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![2, 5, 0, 4, 0, 0], ![5, 4, 1, 2, 1, 1], ![0, 1, 0, 3, 3, 1], ![4, 2, 3, 5, 3, 3], ![0, 1, 3, 3, 1, 0], ![0, 1, 1, 3, 0, 3]] x y

theorem aut6h6aM1482_models : @satisfies _ (Fin 6) aut6h6aM1482 Law1482 :=
  (@Law1482.models_iff (Fin 6) aut6h6aM1482).mpr (by native_decide)

theorem aut6h6aM1482_endo : ∀ i, aut6h6aM1482.IsEndo (aut6h6a.E i) := by decide

/-- A model of equation 3352 on `Fin 6` invariant under aut6h6a. -/
@[reducible]
def aut6h6aM3352 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![2, 2, 2, 2, 5, 4], ![4, 4, 5, 4, 4, 2], ![2, 4, 0, 5, 3, 1], ![5, 5, 4, 5, 2, 5], ![2, 4, 3, 5, 1, 0], ![2, 4, 1, 5, 0, 3]] x y

theorem aut6h6aM3352_models : @satisfies _ (Fin 6) aut6h6aM3352 Law3352 :=
  (@Law3352.models_iff (Fin 6) aut6h6aM3352).mpr (by native_decide)

theorem aut6h6aM3352_endo : ∀ i, aut6h6aM3352.IsEndo (aut6h6a.E i) := by decide

/-- A model of equation 3748 on `Fin 6` invariant under aut6h6a. -/
@[reducible]
def aut6h6aM3748 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![0, 2, 0, 2, 0, 0], ![4, 1, 1, 4, 1, 1], ![0, 4, 0, 5, 2, 2], ![5, 5, 3, 3, 3, 3], ![2, 1, 4, 5, 1, 4], ![2, 4, 5, 3, 5, 3]] x y

theorem aut6h6aM3748_models : @satisfies _ (Fin 6) aut6h6aM3748 Law3748 :=
  (@Law3748.models_iff (Fin 6) aut6h6aM3748).mpr (by native_decide)

theorem aut6h6aM3748_endo : ∀ i, aut6h6aM3748.IsEndo (aut6h6a.E i) := by decide

/-- A model of equation 4321 on `Fin 6` invariant under aut6h6a. -/
@[reducible]
def aut6h6aM4321 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![0, 2, 0, 2, 5, 4], ![4, 1, 5, 4, 1, 2], ![0, 1, 0, 3, 3, 1], ![5, 5, 4, 3, 2, 3], ![0, 1, 3, 3, 1, 0], ![0, 1, 1, 3, 0, 3]] x y

theorem aut6h6aM4321_models : @satisfies _ (Fin 6) aut6h6aM4321 Law4321 :=
  (@Law4321.models_iff (Fin 6) aut6h6aM4321).mpr (by native_decide)

theorem aut6h6aM4321_endo : ∀ i, aut6h6aM4321.IsEndo (aut6h6a.E i) := by decide

/-- A model of equation 4408 on `Fin 6` invariant under aut6h6a. -/
@[reducible]
def aut6h6aM4408 : Magma (Fin 6) := Magma.mk fun x y ↦ ![![2, 2, 2, 2, 5, 4], ![4, 4, 5, 4, 4, 2], ![2, 4, 0, 5, 3, 1], ![5, 5, 4, 5, 2, 5], ![2, 4, 3, 5, 1, 0], ![2, 4, 1, 5, 0, 3]] x y

theorem aut6h6aM4408_models : @satisfies _ (Fin 6) aut6h6aM4408 Law4408 :=
  (@Law4408.models_iff (Fin 6) aut6h6aM4408).mpr (by native_decide)

theorem aut6h6aM4408_endo : ∀ i, aut6h6aM4408.IsEndo (aut6h6a.E i) := by decide
