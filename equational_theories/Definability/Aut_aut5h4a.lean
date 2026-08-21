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
def E : Fin 4 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![1, 3, 0, 2, 4], ![2, 0, 3, 1, 4], ![3, 2, 1, 0, 4]]

def Einv : Fin 4 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![2, 0, 3, 1, 4], ![1, 3, 0, 2, 4], ![3, 2, 1, 0, 4]]

/-- One ordered pair per orbit (7 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 7 → Fin 5 × Fin 5 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (4, 0), (4, 4)]

def tr : Fin 5 → Fin 5 → Fin 7 × Fin 4 := fun x y ↦
  ![![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)], ![(2, 1), (0, 1), (3, 1), (1, 1), (4, 1)], ![(1, 2), (3, 2), (0, 2), (2, 2), (4, 2)], ![(3, 3), (2, 3), (1, 3), (0, 3), (4, 3)], ![(5, 0), (5, 1), (5, 2), (5, 3), (6, 0)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut5h4a

namespace aut5h4a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 7 → Fin 4 := ![0, 0, 0, 0, 0, 0, 0]

def st : Fin 7 → Fin 4 → Fin 4 := fun i j ↦
  ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 0, 0, 0]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut5h4a

/-! ### The sources -/

/-- A model of equation 115 on `Fin 5` invariant under aut5h4a. -/
@[reducible]
def aut5h4aM115 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![1, 2, 4, 3, 0], ![4, 3, 2, 0, 1], ![3, 1, 0, 4, 2], ![0, 4, 1, 2, 3], ![2, 0, 3, 1, 4]] x y

theorem aut5h4aM115_models : @satisfies _ (Fin 5) aut5h4aM115 Law115 :=
  (@Law115.models_iff (Fin 5) aut5h4aM115).mpr (by native_decide)

theorem aut5h4aM115_endo : ∀ i, aut5h4aM115.IsEndo (aut5h4a.E i) := by decide

/-- A model of equation 481 on `Fin 5` invariant under aut5h4a. -/
@[reducible]
def aut5h4aM481 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![4, 0, 1, 3, 2], ![3, 4, 2, 1, 0], ![2, 1, 4, 0, 3], ![0, 2, 3, 4, 1], ![1, 3, 0, 2, 4]] x y

theorem aut5h4aM481_models : @satisfies _ (Fin 5) aut5h4aM481 Law481 :=
  (@Law481.models_iff (Fin 5) aut5h4aM481).mpr (by native_decide)

theorem aut5h4aM481_endo : ∀ i, aut5h4aM481.IsEndo (aut5h4a.E i) := by decide

/-- A model of equation 501 on `Fin 5` invariant under aut5h4a. -/
@[reducible]
def aut5h4aM501 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![3, 1, 4, 2, 0], ![4, 2, 0, 3, 1], ![0, 3, 1, 4, 2], ![1, 4, 2, 0, 3], ![1, 3, 0, 2, 4]] x y

theorem aut5h4aM501_models : @satisfies _ (Fin 5) aut5h4aM501 Law501 :=
  (@Law501.models_iff (Fin 5) aut5h4aM501).mpr (by native_decide)

theorem aut5h4aM501_endo : ∀ i, aut5h4aM501.IsEndo (aut5h4a.E i) := by decide

/-- A model of equation 873 on `Fin 5` invariant under aut5h4a. -/
@[reducible]
def aut5h4aM873 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0], ![4, 2, 0, 1, 3], ![3, 0, 4, 2, 1], ![0, 1, 2, 3, 4]] x y

theorem aut5h4aM873_models : @satisfies _ (Fin 5) aut5h4aM873 Law873 :=
  (@Law873.models_iff (Fin 5) aut5h4aM873).mpr (by native_decide)

theorem aut5h4aM873_endo : ∀ i, aut5h4aM873.IsEndo (aut5h4a.E i) := by decide
