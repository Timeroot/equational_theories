import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: 3-cycle fixing a point of Fin 4

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 4096 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### 3-cycle fixing a point of Fin 4 -/

namespace rot3

/-- The 3 permutations of `Fin 4`, and their inverses. -/
def E : Fin 3 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]]

def Einv : Fin 3 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 3, 1, 2], ![0, 2, 3, 1]]

/-- One ordered pair per orbit (6 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 6 → Fin 4 × Fin 4 := ![(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3)]

def tr : Fin 4 → Fin 4 → Fin 6 × Fin 3 := fun x y ↦
  ![![(0, 0), (1, 0), (1, 1), (1, 2)], ![(2, 0), (3, 0), (4, 0), (5, 0)], ![(2, 1), (5, 1), (3, 1), (4, 1)], ![(2, 2), (4, 2), (5, 2), (3, 2)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end rot3

/-! ### The refuted targets -/

/-- No rot3-invariant operation on `Fin 4` satisfies equation 467. -/
theorem norot3_Law467 : ∀ v : Fin 6 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport rot3.E rot3.tr v)).IsEndo (rot3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport rot3.E rot3.tr v)) Law467 := by
  simp only [Law467.models_iff]
  native_decide

/-- No rot3-invariant operation on `Fin 4` satisfies equation 704. -/
theorem norot3_Law704 : ∀ v : Fin 6 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport rot3.E rot3.tr v)).IsEndo (rot3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport rot3.E rot3.tr v)) Law704 := by
  simp only [Law704.models_iff]
  native_decide

/-- No rot3-invariant operation on `Fin 4` satisfies equation 1279. -/
theorem norot3_Law1279 : ∀ v : Fin 6 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport rot3.E rot3.tr v)).IsEndo (rot3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport rot3.E rot3.tr v)) Law1279 := by
  simp only [Law1279.models_iff]
  native_decide

/-- No rot3-invariant operation on `Fin 4` satisfies equation 1489. -/
theorem norot3_Law1489 : ∀ v : Fin 6 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport rot3.E rot3.tr v)).IsEndo (rot3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport rot3.E rot3.tr v)) Law1489 := by
  simp only [Law1489.models_iff]
  native_decide

/-- No rot3-invariant operation on `Fin 4` satisfies equation 1516. -/
theorem norot3_Law1516 : ∀ v : Fin 6 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport rot3.E rot3.tr v)).IsEndo (rot3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport rot3.E rot3.tr v)) Law1516 := by
  simp only [Law1516.models_iff]
  native_decide

/-! ### The sources -/

/-- A model of equation 1110 on `Fin 4` invariant under rot3. -/
@[reducible]
def rot3M1110 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![2, 3, 0, 1], ![3, 2, 1, 0], ![1, 0, 3, 2]] x y

theorem rot3M1110_models : @satisfies _ (Fin 4) rot3M1110 Law1110 :=
  (@Law1110.models_iff (Fin 4) rot3M1110).mpr (by native_decide)

theorem rot3M1110_endo : ∀ i, rot3M1110.IsEndo (rot3.E i) := by decide

/-! ### The refutations -- 5 cells -/

theorem Equation467_not_definableFrom_Equation1110 :
    ¬ Law467.DefinableFrom Law1110 :=
  not_definableFrom_transport (rot3M1110 : Magma (Fin 4)) rot3M1110_models
    rot3.E rot3.Einv rot3.rep rot3.tr rot3.hl rot3.hr rot3M1110_endo rot3.htr
    norot3_Law467

theorem Equation704_not_definableFrom_Equation1110 :
    ¬ Law704.DefinableFrom Law1110 :=
  not_definableFrom_transport (rot3M1110 : Magma (Fin 4)) rot3M1110_models
    rot3.E rot3.Einv rot3.rep rot3.tr rot3.hl rot3.hr rot3M1110_endo rot3.htr
    norot3_Law704

theorem Equation1279_not_definableFrom_Equation1110 :
    ¬ Law1279.DefinableFrom Law1110 :=
  not_definableFrom_transport (rot3M1110 : Magma (Fin 4)) rot3M1110_models
    rot3.E rot3.Einv rot3.rep rot3.tr rot3.hl rot3.hr rot3M1110_endo rot3.htr
    norot3_Law1279

theorem Equation1489_not_definableFrom_Equation1110 :
    ¬ Law1489.DefinableFrom Law1110 :=
  not_definableFrom_transport (rot3M1110 : Magma (Fin 4)) rot3M1110_models
    rot3.E rot3.Einv rot3.rep rot3.tr rot3.hl rot3.hr rot3M1110_endo rot3.htr
    norot3_Law1489

theorem Equation1516_not_definableFrom_Equation1110 :
    ¬ Law1516.DefinableFrom Law1110 :=
  not_definableFrom_transport (rot3M1110 : Magma (Fin 4)) rot3M1110_models
    rot3.E rot3.Einv rot3.rep rot3.tr rot3.hl rot3.hr rot3M1110_endo rot3.htr
    norot3_Law1516
