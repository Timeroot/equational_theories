import equational_theories.Parastrophes.FiniteSolutions
import equational_theories.Parastrophes.FiniteQuasigroups

/-! One-sided laws that were hidden by two-sided quasigroup counterexamples.
The defining identity supplies a solution; finiteness supplies uniqueness. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

/-- E16 makes each left translation an involution, on arbitrary carriers. -/
@[parastrophe_result] theorem left_term16 :
    UniformTermWitness .all Law16 .left (Lf 0 ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law16.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => (hh y x).symm⟩

/-- Left projection has identity right translations, even when it is not a quasigroup. -/
@[parastrophe_result] theorem right_term4 :
    UniformTermWitness .all Law4 .right (Lf 0 ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law4.models_iff G M).mp h
  exact ⟨fun x y => ((hh x y).trans (hh (M.op x y) y)).symm,
    fun x y => ((hh x y).trans (hh (M.op x y) y)).symm⟩

/-- The E65 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution65_fin :
    UniformTermWitness .fin Law65 .left (Lf 1 ⋆ (Lf 0 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law65.models_iff G M).mp h y x).symm

/-- The E75 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution75_fin :
    UniformTermWitness .fin Law75 .left (Lf 0 ⋆ (Lf 0 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law75.models_iff G M).mp h y x).symm

/-- The E117 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution117_fin :
    UniformTermWitness .fin Law117 .left ((Lf 1 ⋆ Lf 0) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law117.models_iff G M).mp h y x).symm

/-- The E124 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution124_fin :
    UniformTermWitness .fin Law124 .left ((Lf 0 ⋆ Lf 1) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law124.models_iff G M).mp h y x).symm

/-- The E127 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution127_fin :
    UniformTermWitness .fin Law127 .left ((Lf 0 ⋆ Lf 0) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law127.models_iff G M).mp h y x).symm

/-- The E466 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution466_fin :
    UniformTermWitness .fin Law466 .left (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 1))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law466.models_iff G M).mp h y x).symm

/-- The E473 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution473_fin :
    UniformTermWitness .fin Law473 .left (Lf 1 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 1))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law473.models_iff G M).mp h y x).symm

/-- The E474 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution474_fin :
    UniformTermWitness .fin Law474 .left (Lf 1 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 0))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law474.models_iff G M).mp h y x).symm

/-- The E476 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution476_fin :
    UniformTermWitness .fin Law476 .left (Lf 1 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law476.models_iff G M).mp h y x).symm

/-- The E501 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution501_fin :
    UniformTermWitness .fin Law501 .left (Lf 0 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law501.models_iff G M).mp h y x).symm

/-- The E503 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution503_fin :
    UniformTermWitness .fin Law503 .left (Lf 0 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 1))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law503.models_iff G M).mp h y x).symm

/-- The E504 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution504_fin :
    UniformTermWitness .fin Law504 .left (Lf 0 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law504.models_iff G M).mp h y x).symm

/-- The E510 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution510_fin :
    UniformTermWitness .fin Law510 .left (Lf 0 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 1))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law510.models_iff G M).mp h y x).symm

/-- The E513 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution513_fin :
    UniformTermWitness .fin Law513 .left (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law513.models_iff G M).mp h y x).symm

/-- The E669 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution669_fin :
    UniformTermWitness .fin Law669 .left (Lf 1 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law669.models_iff G M).mp h y x).symm

/-- The E670 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution670_fin :
    UniformTermWitness .fin Law670 .left (Lf 1 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 0)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law670.models_iff G M).mp h y x).symm

/-- The E676 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution676_fin :
    UniformTermWitness .fin Law676 .left (Lf 1 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law676.models_iff G M).mp h y x).symm

/-- The E679 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution679_fin :
    UniformTermWitness .fin Law679 .left (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law679.models_iff G M).mp h y x).symm

/-- The E703 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution703_fin :
    UniformTermWitness .fin Law703 .left (Lf 0 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law703.models_iff G M).mp h y x).symm

/-- The E706 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution706_fin :
    UniformTermWitness .fin Law706 .left (Lf 0 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law706.models_iff G M).mp h y x).symm

/-- The E713 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution713_fin :
    UniformTermWitness .fin Law713 .left (Lf 0 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law713.models_iff G M).mp h y x).symm

/-- The E716 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution716_fin :
    UniformTermWitness .fin Law716 .left (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law716.models_iff G M).mp h y x).symm

/-- The E872 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution872_fin :
    UniformTermWitness .fin Law872 .left ((Lf 1 ⋆ Lf 1) ⋆ (Lf 0 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law872.models_iff G M).mp h y x).symm

/-- The E879 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution879_fin :
    UniformTermWitness .fin Law879 .left ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law879.models_iff G M).mp h y x).symm

/-- The E882 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution882_fin :
    UniformTermWitness .fin Law882 .left ((Lf 1 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law882.models_iff G M).mp h y x).symm

/-- The E906 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution906_fin :
    UniformTermWitness .fin Law906 .left ((Lf 0 ⋆ Lf 1) ⋆ (Lf 1 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law906.models_iff G M).mp h y x).symm

/-- The E916 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution916_fin :
    UniformTermWitness .fin Law916 .left ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 1)) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law916.models_iff G M).mp h y x).symm

/-- The E1075 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1075_fin :
    UniformTermWitness .fin Law1075 .left ((Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1075.models_iff G M).mp h y x).symm

/-- The E1082 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1082_fin :
    UniformTermWitness .fin Law1082 .left ((Lf 1 ⋆ (Lf 0 ⋆ Lf 1)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1082.models_iff G M).mp h y x).symm

/-- The E1085 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1085_fin :
    UniformTermWitness .fin Law1085 .left ((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1085.models_iff G M).mp h y x).symm

/-- The E1109 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1109_fin :
    UniformTermWitness .fin Law1109 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 1)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1109.models_iff G M).mp h y x).symm

/-- The E1112 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1112_fin :
    UniformTermWitness .fin Law1112 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1112.models_iff G M).mp h y x).symm

/-- The E1119 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1119_fin :
    UniformTermWitness .fin Law1119 .left ((Lf 0 ⋆ (Lf 0 ⋆ Lf 1)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1119.models_iff G M).mp h y x).symm

/-- The E1122 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1122_fin :
    UniformTermWitness .fin Law1122 .left ((Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1122.models_iff G M).mp h y x).symm

/-- The E1278 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1278_fin :
    UniformTermWitness .fin Law1278 .left (((Lf 1 ⋆ Lf 1) ⋆ Lf 0) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1278.models_iff G M).mp h y x).symm

/-- The E1285 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1285_fin :
    UniformTermWitness .fin Law1285 .left (((Lf 1 ⋆ Lf 0) ⋆ Lf 1) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1285.models_iff G M).mp h y x).symm

/-- The E1288 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1288_fin :
    UniformTermWitness .fin Law1288 .left (((Lf 1 ⋆ Lf 0) ⋆ Lf 0) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1288.models_iff G M).mp h y x).symm

/-- The E1312 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1312_fin :
    UniformTermWitness .fin Law1312 .left (((Lf 0 ⋆ Lf 1) ⋆ Lf 1) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1312.models_iff G M).mp h y x).symm

/-- The E1315 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1315_fin :
    UniformTermWitness .fin Law1315 .left (((Lf 0 ⋆ Lf 1) ⋆ Lf 0) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1315.models_iff G M).mp h y x).symm

/-- The E1322 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1322_fin :
    UniformTermWitness .fin Law1322 .left (((Lf 0 ⋆ Lf 0) ⋆ Lf 1) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1322.models_iff G M).mp h y x).symm

/-- The E1325 identity gives a uniform left division on finite carriers. -/
@[parastrophe_result] theorem left_solution1325_fin :
    UniformTermWitness .fin Law1325 .left (((Lf 0 ⋆ Lf 0) ⋆ Lf 0) ⋆ Lf 1) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((@Law1325.models_iff G M).mp h y x).symm

/-- In E1525, L_(y*y), L_y and squaring compose to the identity.
On a finite carrier every factor is bijective. -/
@[parastrophe_result] theorem left_quasigroup1525_fin :
    SideQuasigroupLaw .fin Law1525 .left := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (@Law1525.models_iff G M).mp h
  intro y
  exact bijective_middle (M.op (M.op y y)) (M.op y) (fun x => M.op x x)
    (fun x => (hh x y).symm)

/-- E1793 gives inverse translations at each product u*v and v*u.
Every element is a product, so this is a uniform left division on all carriers. -/
@[parastrophe_result] theorem left_term1793 :
    UniformTermWitness .all Law1793 .left
      ((((Lf 0 ⋆ Lf 0) ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law1793.models_iff G M).mp h
  constructor <;> intro x y
  · have he := (hh y (M.op x x) (M.op (M.op x x) x)).symm
    have hx := (hh x x x).symm
    rw [hx] at he
    exact he
  · have he := (hh y (M.op (M.op x x) x) (M.op x x)).symm
    have hx := (hh x x x).symm
    rw [hx] at he
    exact he

end Parastrophes.Catalogue
