import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 24 on Fin 8

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 4096 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 24 on Fin 8 -/

namespace aut8h24a

/-- The 24 permutations of `Fin 8`, and their inverses. -/
def E : Fin 24 → Fin 8 → Fin 8 := ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 6, 7, 4, 5], ![0, 5, 2, 6, 3, 7, 4, 1], ![0, 5, 2, 6, 4, 1, 3, 7], ![0, 7, 2, 4, 3, 5, 6, 1], ![0, 7, 2, 4, 6, 1, 3, 5], ![1, 0, 3, 2, 4, 5, 6, 7], ![1, 0, 3, 2, 6, 7, 4, 5], ![1, 5, 3, 6, 2, 7, 4, 0], ![1, 5, 3, 6, 4, 0, 2, 7], ![1, 7, 3, 4, 2, 5, 6, 0], ![1, 7, 3, 4, 6, 0, 2, 5], ![5, 0, 6, 2, 3, 7, 4, 1], ![5, 0, 6, 2, 4, 1, 3, 7], ![5, 1, 6, 3, 2, 7, 4, 0], ![5, 1, 6, 3, 4, 0, 2, 7], ![5, 7, 6, 4, 2, 1, 3, 0], ![5, 7, 6, 4, 3, 0, 2, 1], ![7, 0, 4, 2, 3, 5, 6, 1], ![7, 0, 4, 2, 6, 1, 3, 5], ![7, 1, 4, 3, 2, 5, 6, 0], ![7, 1, 4, 3, 6, 0, 2, 5], ![7, 5, 4, 6, 2, 1, 3, 0], ![7, 5, 4, 6, 3, 0, 2, 1]]

def Einv : Fin 24 → Fin 8 → Fin 8 := ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 6, 7, 4, 5], ![0, 7, 2, 4, 6, 1, 3, 5], ![0, 5, 2, 6, 4, 1, 3, 7], ![0, 7, 2, 4, 3, 5, 6, 1], ![0, 5, 2, 6, 3, 7, 4, 1], ![1, 0, 3, 2, 4, 5, 6, 7], ![1, 0, 3, 2, 6, 7, 4, 5], ![7, 0, 4, 2, 6, 1, 3, 5], ![5, 0, 6, 2, 4, 1, 3, 7], ![7, 0, 4, 2, 3, 5, 6, 1], ![5, 0, 6, 2, 3, 7, 4, 1], ![1, 7, 3, 4, 6, 0, 2, 5], ![1, 5, 3, 6, 4, 0, 2, 7], ![7, 1, 4, 3, 6, 0, 2, 5], ![5, 1, 6, 3, 4, 0, 2, 7], ![7, 5, 4, 6, 3, 0, 2, 1], ![5, 7, 6, 4, 3, 0, 2, 1], ![1, 7, 3, 4, 2, 5, 6, 0], ![1, 5, 3, 6, 2, 7, 4, 0], ![7, 1, 4, 3, 2, 5, 6, 0], ![5, 1, 6, 3, 2, 7, 4, 0], ![7, 5, 4, 6, 2, 1, 3, 0], ![5, 7, 6, 4, 2, 1, 3, 0]]

/-- One ordered pair per orbit (8 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 8 → Fin 8 × Fin 8 := ![(0, 0), (0, 1), (0, 2), (0, 3), (2, 0), (2, 1), (2, 2), (2, 3)]

def tr : Fin 8 → Fin 8 → Fin 8 × Fin 24 := fun x y ↦
  ![![(0, 0), (1, 0), (2, 0), (3, 0), (3, 4), (1, 2), (3, 2), (1, 4)], ![(1, 6), (0, 6), (3, 6), (2, 6), (3, 10), (1, 8), (3, 8), (1, 10)], ![(4, 0), (5, 0), (6, 0), (7, 0), (7, 4), (5, 2), (7, 2), (5, 4)], ![(5, 6), (4, 6), (7, 6), (6, 6), (7, 10), (5, 8), (7, 8), (5, 10)], ![(5, 18), (5, 20), (7, 18), (7, 20), (6, 18), (5, 22), (7, 22), (4, 18)], ![(1, 12), (1, 14), (3, 12), (3, 14), (3, 16), (0, 12), (2, 12), (1, 16)], ![(5, 12), (5, 14), (7, 12), (7, 14), (7, 16), (4, 12), (6, 12), (5, 16)], ![(1, 18), (1, 20), (3, 18), (3, 20), (2, 18), (1, 22), (3, 22), (0, 18)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut8h24a

namespace aut8h24a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 8 → Fin 24 := ![0, 0, 0, 0, 0, 0, 0, 0]

def st : Fin 8 → Fin 24 → Fin 24 := fun i j ↦
  ![![0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22], ![0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22], ![0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22], ![0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18], ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut8h24a

/-! ### The sources -/

/-- A model of equation 3272 on `Fin 8` invariant under aut8h24a. -/
@[reducible]
def aut8h24aM3272 : Magma (Fin 8) := Magma.mk fun x y ↦ ![![0, 2, 0, 1, 7, 2, 5, 2], ![3, 1, 0, 1, 7, 3, 5, 3], ![0, 2, 0, 1, 7, 2, 5, 2], ![3, 1, 0, 1, 7, 3, 5, 3], ![4, 4, 0, 1, 7, 4, 5, 7], ![6, 6, 0, 1, 7, 5, 5, 6], ![6, 6, 0, 1, 7, 5, 5, 6], ![4, 4, 0, 1, 7, 4, 5, 7]] x y

theorem aut8h24aM3272_models : @satisfies _ (Fin 8) aut8h24aM3272 Law3272 :=
  (@Law3272.models_iff (Fin 8) aut8h24aM3272).mpr (by native_decide)

theorem aut8h24aM3272_endo : ∀ i, aut8h24aM3272.IsEndo (aut8h24a.E i) := by decide

/-- A model of equation 3748 on `Fin 8` invariant under aut8h24a. -/
@[reducible]
def aut8h24aM3748 : Magma (Fin 8) := Magma.mk fun x y ↦ ![![0, 2, 0, 0, 0, 2, 0, 2], ![3, 1, 1, 1, 1, 3, 1, 3], ![0, 3, 0, 2, 2, 6, 2, 4], ![2, 1, 3, 1, 3, 6, 3, 4], ![2, 3, 4, 4, 7, 6, 4, 7], ![6, 6, 5, 5, 5, 5, 5, 6], ![2, 3, 6, 6, 6, 5, 5, 4], ![4, 4, 7, 7, 7, 4, 7, 7]] x y

theorem aut8h24aM3748_models : @satisfies _ (Fin 8) aut8h24aM3748 Law3748 :=
  (@Law3748.models_iff (Fin 8) aut8h24aM3748).mpr (by native_decide)

theorem aut8h24aM3748_endo : ∀ i, aut8h24aM3748.IsEndo (aut8h24a.E i) := by decide
