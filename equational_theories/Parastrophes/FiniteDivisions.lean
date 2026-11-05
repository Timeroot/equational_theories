import equational_theories.Parastrophes.DivisionTerms
import equational_theories.Parastrophes.FiniteQuasigroups
import equational_theories.Spectrum.Equation667Division

/-! Fixed division terms for finite E63 and E667; their lengths do not depend on
the order of the model. These improve the generic per-model factorial construction. -/
namespace Parastrophes.Catalogue
open FreeMagma

/-- In E63, two successive left divisions recover right division. -/
@[parastrophe_result] theorem right_term63_fin :
    UniformTermWitness .fin Law63 .right
      ((Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 0)) := by
  intro G M hG h
  have hQ := quasigroup63_fin G M hG h
  have hD := left_term63_fin G M hG h
  let D := termMagma M (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))
  have hi (x y : G) : D.op (M.op x y) (D.op (M.op x y) y) = x := by
    let c := M.op x y
    have he : M.op c (M.op c x) = y :=
      (hQ.1 x).1 ((@Law63.models_iff G M).mp h c x).symm
    have hh := congrArg (D.op c) he
    change D.op c (M.op c (M.op c x)) = D.op c y at hh
    rw [hD.2] at hh
    rw [← hh, hD.2]
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := (hQ.2 y).2 x
    exact congrArg (fun z => M.op z y) (hi a y)
  · exact hi

/-- The left division term used throughout the existing finite E667 proofs. -/
@[parastrophe_result] theorem left_term667_fin :
    UniformTermWitness .fin Law667 .left
      (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0)) := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law667.models_iff G M).mp h
  exact ⟨Spectrum.E667.Division.mul_op hh, Spectrum.E667.Division.op_mul hh⟩

/-- In E667, x / y = (x*x) left-divide (x left-divide y). -/
@[parastrophe_result] theorem right_term667_fin :
    UniformTermWitness .fin Law667 .right
      ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0)) ⋆
        (((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0)) ⋆
          (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ Lf 0))) := by
  intro G M hG h
  have hQ := quasigroup667_fin G M hG h
  have hD := left_term667_fin G M hG h
  let D := termMagma M (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0))
  have hi (x y : G) :
      D.op (M.op (M.op x y) (M.op x y)) (D.op (M.op x y) y) = x := by
    let c := M.op x y
    have he : M.op c (M.op (M.op c c) x) = y :=
      (hQ.1 x).1 ((@Law667.models_iff G M).mp h c x).symm
    have hh := congrArg (D.op c) he
    change D.op c (M.op c (M.op (M.op c c) x)) = D.op c y at hh
    rw [hD.2] at hh
    rw [← hh, hD.2]
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := (hQ.2 y).2 x
    exact congrArg (fun z => M.op z y) (hi a y)
  · exact hi

end Parastrophes.Catalogue
