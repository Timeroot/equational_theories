import equational_theories.Parastrophes.Attributes
import equational_theories.Superposition
import equational_theories.Equations.All

/-! E510 has genuine left division even on infinite carriers. The square-map
identity is extracted from the existing checked parastrophic construction. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

theorem square510 {G : Type} [Magma G] (h : Equation510 G) (x y : G) :
    x ◇ (y ◇ y) = (x ◇ y) ◇ (x ◇ y) := by
  have ef5 (X0 X1 : G) : X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have ef7 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := superpose ef5 ef5
  have ef8 (X0 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    exact superpose ef7 ef5
  have ef10 (X0 : G) : X0 ◇ X0 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0 := by
    exact superpose ef8 ef5
  have ef12 (X0 : G) :
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    exact superpose ef10 ef5
  have ef13 (X0 : G) :
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    exact superpose ef7 ef12
  have ef15 (X0 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    exact superpose ef13 ef10
  have ef16 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 ◇ (X0 ◇ X0) := by
    exact superpose ef13 ef8
  have ef20 (X0 : G) : X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    exact superpose ef13 ef7
  have ef21 (X0 X1 : G) :
      ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 ◇ (X1 ◇ (X1 ◇ X0)) := by
    exact superpose ef13 ef5
  have ef24 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 ◇ (X0 ◇ (X0 ◇ X0)) := by
    exact superpose ef16 ef15
  have ef33 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    exact superpose ef16 ef8
  have ef40 (X0 : G) :
      X0 ◇ X0 = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇
      (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    exact superpose ef16 ef8
  have ef43 (X0 : G) :
      X0 ◇ X0 = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇
      ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    exact superpose ef16 ef40
  have ef48 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    exact superpose ef24 ef33
  have ef52 (X0 : G) :
      X0 ◇ X0 = (X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    exact superpose ef24 ef43
  have ef56 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0 := by
    exact superpose ef48 ef52
  have ef166 (X0 X1 X2 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = X2 ◇ (X2 ◇ (X2 ◇ X1)) := superpose ef21 ef21
  have ef177 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    exact superpose ef21 ef20
  have ef179 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    exact superpose ef21 ef8
  have ef215 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    exact superpose ef16 ef179
  have ef265 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0) := by
    exact superpose ef5 ef177
  have ef632 (X0 X1 : G) : X1 ◇ X1 = (X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1 := by
    exact superpose ef166 ef56
  have ef739 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)) := by
    exact superpose ef5 ef632
  have ef861 (X0 X1 : G) :
      X1 ◇ (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X0) := by
    exact superpose ef5 ef215
  have ef920 (X0 X1 : G) :
      X1 ◇ (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X0) := by
    exact superpose ef739 ef861
  have ef1274 (X0 X1 : G) :
      (X0 ◇ X1) ◇ (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇
      (X0 ◇ X1) := by
    exact superpose ef265 ef632
  have ef1275 (X0 X1 : G) :
      (X0 ◇ X1) ◇ (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1) := by
    exact superpose ef739 ef1274
  have ef1322 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = (X0 ◇ X1) ◇ (X0 ◇ X1) := by
    exact superpose ef920 ef1275
  exact ef1322 x y

/-- Squaring commutes with left translations in E510, so its right inverse
also inverts on the other side, without a finite-carrier assumption. -/
@[parastrophe_result] theorem left_term510_all :
    UniformTermWitness .all Law510 .left (Lf 0 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 1))) := by
  intro G M _ h
  letI : Magma G := M
  have hh := (@Law510.models_iff G M).mp h
  constructor
  · intro x y
    exact (hh y x).symm
  · intro x y
    change x ◇ (x ◇ ((x ◇ y) ◇ (x ◇ y))) = y
    rw [← square510 hh]
    exact (hh y x).symm

end Parastrophes.Catalogue
