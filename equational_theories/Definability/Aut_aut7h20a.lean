import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: group of order 20 on Fin 7

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 27216 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### group of order 20 on Fin 7 -/

namespace aut7h20a

/-- The 20 permutations of `Fin 7`, and their inverses. -/
def E : Fin 20 → Fin 7 → Fin 7 := ![![0, 1, 2, 3, 4, 5, 6], ![0, 2, 4, 1, 3, 5, 6], ![0, 3, 1, 4, 2, 5, 6], ![0, 4, 3, 2, 1, 5, 6], ![1, 0, 4, 3, 2, 5, 6], ![1, 2, 3, 4, 0, 5, 6], ![1, 3, 0, 2, 4, 5, 6], ![1, 4, 2, 0, 3, 5, 6], ![2, 0, 3, 1, 4, 5, 6], ![2, 1, 0, 4, 3, 5, 6], ![2, 3, 4, 0, 1, 5, 6], ![2, 4, 1, 3, 0, 5, 6], ![3, 0, 2, 4, 1, 5, 6], ![3, 1, 4, 2, 0, 5, 6], ![3, 2, 1, 0, 4, 5, 6], ![3, 4, 0, 1, 2, 5, 6], ![4, 0, 1, 2, 3, 5, 6], ![4, 1, 3, 0, 2, 5, 6], ![4, 2, 0, 3, 1, 5, 6], ![4, 3, 2, 1, 0, 5, 6]]

def Einv : Fin 20 → Fin 7 → Fin 7 := ![![0, 1, 2, 3, 4, 5, 6], ![0, 3, 1, 4, 2, 5, 6], ![0, 2, 4, 1, 3, 5, 6], ![0, 4, 3, 2, 1, 5, 6], ![1, 0, 4, 3, 2, 5, 6], ![4, 0, 1, 2, 3, 5, 6], ![2, 0, 3, 1, 4, 5, 6], ![3, 0, 2, 4, 1, 5, 6], ![1, 3, 0, 2, 4, 5, 6], ![2, 1, 0, 4, 3, 5, 6], ![3, 4, 0, 1, 2, 5, 6], ![4, 2, 0, 3, 1, 5, 6], ![1, 4, 2, 0, 3, 5, 6], ![4, 1, 3, 0, 2, 5, 6], ![3, 2, 1, 0, 4, 5, 6], ![2, 3, 4, 0, 1, 5, 6], ![1, 2, 3, 4, 0, 5, 6], ![3, 1, 4, 2, 0, 5, 6], ![2, 4, 1, 3, 0, 5, 6], ![4, 3, 2, 1, 0, 5, 6]]

/-- One ordered pair per orbit (10 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 10 → Fin 7 × Fin 7 := ![(0, 0), (0, 1), (0, 5), (0, 6), (5, 0), (5, 5), (5, 6), (6, 0), (6, 5), (6, 6)]

def tr : Fin 7 → Fin 7 → Fin 10 × Fin 20 := fun x y ↦
  ![![(0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, 0)], ![(1, 4), (0, 4), (1, 5), (1, 6), (1, 7), (2, 4), (3, 4)], ![(1, 8), (1, 9), (0, 8), (1, 10), (1, 11), (2, 8), (3, 8)], ![(1, 12), (1, 13), (1, 14), (0, 12), (1, 15), (2, 12), (3, 12)], ![(1, 16), (1, 17), (1, 18), (1, 19), (0, 16), (2, 16), (3, 16)], ![(4, 0), (4, 4), (4, 8), (4, 12), (4, 16), (5, 0), (6, 0)], ![(7, 0), (7, 4), (7, 8), (7, 12), (7, 16), (8, 0), (9, 0)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end aut7h20a

namespace aut7h20a

/-- For each orbit, the permutation `tr` records at its representative, and the one it
records at that representative's image under each `E j`. -/
def z : Fin 10 → Fin 20 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def st : Fin 10 → Fin 20 → Fin 20 := fun i j ↦
  ![![0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], ![0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], ![0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], ![0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] i j

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide

end aut7h20a

/-! ### The sources -/

/-- A model of equation 1682 on `Fin 7` invariant under aut7h20a. -/
@[reducible]
def aut7h20aM1682 : Magma (Fin 7) := Magma.mk fun x y ↦ ![![0, 2, 4, 1, 3, 0, 5], ![4, 1, 3, 0, 2, 1, 5], ![3, 0, 2, 4, 1, 2, 5], ![2, 4, 1, 3, 0, 3, 5], ![1, 3, 0, 2, 4, 4, 5], ![6, 6, 6, 6, 6, 5, 6], ![0, 1, 2, 3, 4, 6, 5]] x y

theorem aut7h20aM1682_models : @satisfies _ (Fin 7) aut7h20aM1682 Law1682 :=
  (@Law1682.models_iff (Fin 7) aut7h20aM1682).mpr (by native_decide)

theorem aut7h20aM1682_endo : ∀ i, aut7h20aM1682.IsEndo (aut7h20a.E i) := by decide
