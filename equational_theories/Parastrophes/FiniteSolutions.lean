import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-! A uniform one-sided inverse term is automatically two-sided on finite
carriers. This does not assume, or assert, cancellation on the other side. -/
namespace Parastrophes
open Law FreeMagma

/-- A fixed term solving every left division equation works uniformly on all
finite models: a surjective translation of a finite carrier is injective. -/
theorem uniform_left_of_solution {L t}
    (hs : ∀ (G : Type) (M : Magma G), @satisfies _ G M L →
      ∀ x y, M.op x ((termMagma M t).op x y) = y) :
    UniformTermWitness .fin L .left t := by
  intro G M hG h
  letI : Finite G := hG
  have hh := hs G M h
  refine ⟨hh, fun x y => ?_⟩
  have hi : Function.Injective (M.op x) :=
    Finite.injective_iff_surjective.mpr (fun z => ⟨(termMagma M t).op x z, hh x z⟩)
  exact hi (hh x (M.op x y))

namespace Catalogue

/-- E464 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term464_fin :
    UniformTermWitness .fin Law464 .left (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law464.models_iff G M).mp h y x).symm

/-- E467 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term467_fin :
    UniformTermWitness .fin Law467 .left (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law467.models_iff G M).mp h y x).symm

/-- E677 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term677_fin :
    UniformTermWitness .fin Law677 .left (Lf 1 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law677.models_iff G M).mp h y x).symm

/-- E704 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term704_fin :
    UniformTermWitness .fin Law704 .left (Lf 0 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law704.models_iff G M).mp h y x).symm

/-- E870 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term870_fin :
    UniformTermWitness .fin Law870 .left ((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ Lf 0)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law870.models_iff G M).mp h y x).symm

/-- E873 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term873_fin :
    UniformTermWitness .fin Law873 .left ((Lf 1 ⋆ Lf 1) ⋆ (Lf 0 ⋆ Lf 0)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law873.models_iff G M).mp h y x).symm

/-- E907 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term907_fin :
    UniformTermWitness .fin Law907 .left ((Lf 0 ⋆ Lf 1) ⋆ (Lf 1 ⋆ Lf 0)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law907.models_iff G M).mp h y x).symm

/-- E1076 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1076_fin :
    UniformTermWitness .fin Law1076 .left ((Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1076.models_iff G M).mp h y x).symm

/-- E1083 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1083_fin :
    UniformTermWitness .fin Law1083 .left ((Lf 1 ⋆ (Lf 0 ⋆ Lf 1)) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1083.models_iff G M).mp h y x).symm

/-- E1110 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1110_fin :
    UniformTermWitness .fin Law1110 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 1)) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1110.models_iff G M).mp h y x).symm

/-- E1276 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1276_fin :
    UniformTermWitness .fin Law1276 .left (((Lf 1 ⋆ Lf 1) ⋆ Lf 1) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1276.models_iff G M).mp h y x).symm

/-- E1279 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1279_fin :
    UniformTermWitness .fin Law1279 .left (((Lf 1 ⋆ Lf 1) ⋆ Lf 0) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1279.models_iff G M).mp h y x).symm

/-- E1286 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1286_fin :
    UniformTermWitness .fin Law1286 .left (((Lf 1 ⋆ Lf 0) ⋆ Lf 1) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1286.models_iff G M).mp h y x).symm

/-- E1313 explicitly solves every left division equation by a fixed term. -/
@[parastrophe_result] theorem left_term1313_fin :
    UniformTermWitness .fin Law1313 .left (((Lf 0 ⋆ Lf 1) ⋆ Lf 1) ⋆ Lf 0) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1313.models_iff G M).mp h y x).symm

end Catalogue
end Parastrophes
