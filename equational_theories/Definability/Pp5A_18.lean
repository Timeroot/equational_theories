import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq32
    | exact resolve eq32 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq69
    | exact resolve eq69 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq507 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq500 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq500
    | (have j0 := eq500 X0 X1
       grind)
    | exact resolve eq500 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq1971 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq507 x y
       grind)
    | exact superpose eq507 eq16
    | (have j1 := eq507 x y
       grind)
    | exact resolve eq16 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1993 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq507 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq8517 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq502
    | exact resolve eq502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq8738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8517 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8517
    | (have j0 := eq8517 X0 X1
       grind)
    | exact resolve eq8517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8517
  have eq51292 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1971
       have i₂ := eq8738 y x
       grind)
    | exact superpose eq8738 eq1971
    | (have j1 := eq8738 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq1971
       have r₂ := eq8738 y x
       grind)
    | (have r₁ := eq1971
       have r₂ := eq8738 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1971
       have r₂ := eq8738 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1971 eq8738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971 eq8738
  have eq51293 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq51292
  have eq61962 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1993 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq1993
    | (have j0 := eq1993 (τ X1) (τ X0)
       grind)
    | exact resolve eq1993 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq62038 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61962 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq61962
    | (have j0 := eq61962 X0 X1
       grind)
    | exact resolve eq61962 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61962
  have eq62075 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62038 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq62038
    | (have j0 := eq62038 X0 X1
       grind)
    | exact resolve eq62038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62038
  have eq62106 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62075 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq62075
    | (have j0 := eq62075 X0 X1
       grind)
    | exact resolve eq62075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62075
  have eq62133 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62106 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62106
    | (have j0 := eq62106 X0 X1
       grind)
    | exact resolve eq62106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62106
  have eq62155 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62133 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq62133
    | (have j0 := eq62133 X0 X1
       grind)
    | exact resolve eq62133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62133
  have eq62176 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62155 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq62155
    | (have j0 := eq62155 X0 X1
       grind)
    | exact resolve eq62155 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq62155
  have eq62192 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62176 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq62176
    | (have j0 := eq62176 X0 X1
       grind)
    | exact resolve eq62176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62176
  have eq62206 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62192 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq62192
    | (have j0 := eq62192 X0 X1
       grind)
    | exact resolve eq62192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62192
  have eq62216 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62206 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62206
    | (have j0 := eq62206 X0 X1
       grind)
    | exact resolve eq62206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62206
  have eq106702 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51293
       grind)
    | exact superpose eq51293 eq16
    | exact resolve eq16 eq51293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51293
  have eq106703 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq106702
       have r₂ := eq78 x
       grind)
    | exact resolve eq106702 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106702
  have eq106706 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq106703
       grind)
    | exact superpose eq106703 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq106703
       grind)
    | exact resolve eq12 eq106703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106703
  have eq106808 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq106706
  have eq106829 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1993 x y
       have i₂ := eq106808
       grind)
    | exact superpose eq106808 eq1993
    | (have j0 := eq1993 x y
       grind)
    | exact resolve eq1993 eq106808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq106808
  have eq106857 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq106829
  have eq106858 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq106857
  have eq106866 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106858
       grind)
    | exact superpose eq106858 eq16
    | exact resolve eq16 eq106858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106869 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95 x (σ y)
       have i₂ := eq106858
       grind)
    | exact superpose eq106858 eq95
    | (have j0 := eq95 x (σ y)
       grind)
    | (have r₁ := eq95 x (σ y)
       have r₂ := eq106858
       grind)
    | exact resolve eq95 eq106858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq106858
  have eq107014 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq106869
  have eq107076 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq107014
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq107014
    | exact resolve eq107014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107014
  have eq107681 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq107076
       grind)
    | exact superpose eq107076 eq10
    | exact resolve eq10 eq107076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107076
  have eq107971 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq107681
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq107681
    | exact resolve eq107681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107681
  have eq107973 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107971
       grind)
    | exact superpose eq107971 eq16
    | exact resolve eq16 eq107971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107971
  have eq107974 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq107973
       have r₂ := eq78 x
       grind)
    | exact resolve eq107973 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107973
  have eq107988 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq107974
       grind)
    | exact superpose eq107974 eq10
    | exact resolve eq10 eq107974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107974
  have eq108282 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq107988
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq107988
    | exact resolve eq107988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107988
  have eq108309 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq62216 y x
       have i₂ := eq108282
       grind)
    | exact superpose eq108282 eq62216
    | (have j0 := eq62216 y x
       grind)
    | (have r₁ := eq62216 y x
       have r₂ := eq108282
       grind)
    | exact resolve eq62216 eq108282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62216 eq108282
  have eq108319 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq108309
  have eq108323 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108319
       grind)
    | exact superpose eq108319 eq16
    | exact resolve eq16 eq108319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108319
  have eq108326 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq108323
       have r₂ := eq78 x
       grind)
    | exact resolve eq108323 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108323
  have eq108327 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106866
       have i₂ := eq108326
       grind)
    | exact superpose eq108326 eq106866
    | exact resolve eq106866 eq108326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106866
  have eq108433 : (σ x) = (σ y) := by grind
  clear eq108327
  have eq108448 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108433
       grind)
    | exact superpose eq108433 eq16
    | exact resolve eq16 eq108433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108433
  have eq108743 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq108448
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq108448
    | exact resolve eq108448 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq108448
  have eq108744 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq108743
       have i₂ := eq108326
       grind)
    | exact superpose eq108326 eq108743
    | exact resolve eq108743 eq108326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108326 eq108743
  have eq108745 : False := by grind
  exact eq108745

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_x_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq83 y x
       grind)
    | exact superpose eq83 eq75
    | (have j1 := eq83 y x
       grind)
    | exact resolve eq75 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq420 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq428 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq13
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq420 X0
       grind)
    | exact resolve eq13 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq435 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq113 eq83
    | (have j0 := eq83 (σ y) x
       grind)
    | exact resolve eq83 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq827 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq824
       have r₂ := eq27
       grind)
    | exact resolve eq824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq840 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq827 eq435
    | exact resolve eq435 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq861 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq840 eq88
    | exact resolve eq88 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq840
  have eq865 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq861
    | exact resolve eq861 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq861
  have eq868 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83 y y
       have i₂ := eq865
       grind)
    | exact superpose eq865 eq83
    | (have j0 := eq83 y x
       grind)
    | exact resolve eq83 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq869 : y = (M.op y y) := by grind
  clear eq868
  have eq888 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq14
    | exact resolve eq14 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq14
    | exact resolve eq14 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 : G, y = (k y (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq68 y y X0
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq68
    | exact resolve eq68 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq898 : y = (k y y) := by
    first
    | (have i₁ := eq435 y
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq435
    | exact resolve eq435 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq869
  have eq904 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq76
    | exact resolve eq76 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq898
  have eq908 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq904
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq904
    | exact resolve eq904 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq926 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq908 eq83
    | (have j0 := eq83 (σ y) x
       grind)
    | exact resolve eq83 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq908
  have eq927 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq926
  have eq977 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq889 (M.op y X0)
       have i₂ := eq888 X0
       grind)
    | exact superpose eq888 eq889
    | exact resolve eq889 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : ∀ X0 : G, y = (k y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq894 X0
       have i₂ := eq977 X0
       grind)
    | exact superpose eq977 eq894
    | exact resolve eq894 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1125 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq888 X0
       have i₂ := eq977 X0
       grind)
    | exact superpose eq977 eq888
    | exact resolve eq888 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq977
  have eq1153 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq889 X0
       have i₂ := eq1125 X0
       grind)
    | exact superpose eq1125 eq889
    | exact resolve eq889 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1186 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1124 X0
       have i₂ := eq1153 X0
       grind)
    | exact superpose eq1153 eq1124
    | exact resolve eq1124 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1187 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1125 X0
       have i₂ := eq1153 X0
       grind)
    | exact superpose eq1153 eq1125
    | exact resolve eq1125 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq1153
  have eq1253 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq1186 (τ X0)
       grind)
    | exact superpose eq1186 eq38
    | exact resolve eq38 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1186
  have eq1260 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1253 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1253
    | (have j0 := eq1253 X0
       grind)
    | exact resolve eq1253 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1271 : y = (M.op x y) := by
    first
    | (have i₁ := eq1187 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1187
    | (have j0 := eq1187 x
       grind)
    | exact resolve eq1187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1187
  have eq1356 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1271 eq20
    | exact resolve eq20 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1271
  have eq1398 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1356
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1356
    | exact resolve eq1356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1356
  have eq1420 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1398 eq26
    | exact resolve eq26 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1442 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1398 eq927
    | exact resolve eq927 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1457 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1398 eq1260
    | exact resolve eq1260 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq1398
  have eq1540 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1442 eq12
    | (have j0 := eq12 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) x
       have r₂ := eq1442
       grind)
    | exact resolve eq12 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1553 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1554 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1457 eq1553
    | (have j0 := eq1553 X0
       grind)
    | exact resolve eq1553 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq1553
  have eq2316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1554 eq1420
    | (have j1 := eq1554 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1420 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq2333 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2316
       have r₂ := eq27
       grind)
    | exact resolve eq2316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq2533 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2333 eq1420
    | exact resolve eq1420 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq2333
  have eq2540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1442 eq2533
    | exact resolve eq2533 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq2533
  have eq2553 : False := by grind
  exact eq2553

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq222 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq227 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq51
    | exact resolve eq51 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq233 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq227
    | (have j0 := eq227 (σ y)
       grind)
    | exact resolve eq227 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq238 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq233
    | exact resolve eq233 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq233 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq233
       grind)
    | exact resolve eq13 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq242 : (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq239
  have eq243 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq238
  have eq244 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq242
    | exact resolve eq242 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq247 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq244
  have eq249 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq13
    | (have r₁ := eq13 X0 (M.op (M.op x X0) (M.op x y))
       have r₂ := eq53 X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq252 : ∀ X0 : G, (k X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq249 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq260 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq54
    | exact resolve eq54 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq126
  have eq557 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq785 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq260 sF2
       have i₂ := eq557 sF2
       grind)
    | exact superpose eq557 eq260
    | exact resolve eq260 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq798 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq785 eq243
    | exact resolve eq243 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq799 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq785 eq247
    | exact resolve eq247 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq785
  have eq829 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq799
  have eq830 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq798
  have eq831 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq830
    | exact resolve eq830 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq833 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq831 eq27
    | exact resolve eq27 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1068 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq829 eq99
    | exact resolve eq99 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq829
  have eq1071 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1068
  have eq1078 : x = (M.op x y) := by
    first
    | (have r₁ := eq1071
       have r₂ := eq833
       grind)
    | exact resolve eq1071 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq1071
  have eq1081 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1078 eq20
    | exact resolve eq20 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1091 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq1078 eq222
    | exact resolve eq222 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq1098 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1081
    | exact resolve eq1081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1100 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1098 eq26
    | exact resolve eq26 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1199 : ∀ X0 : G, (k X0 (M.op (M.op x X0) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1078 eq252
    | exact resolve eq252 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq1201 : x = (k x x) := by
    first
    | (have i₁ := eq1199 x
       have i₂ := eq557 x
       grind)
    | exact superpose eq557 eq1199
    | exact resolve eq1199 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq1199
  have eq1209 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq43
    | exact resolve eq43 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1210 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1211 : x = (M.op x x) := by grind
  clear eq1210
  have eq1213 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1098 eq1209
    | exact resolve eq1209 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1214 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1213
    | exact resolve eq1213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1215 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1098 eq1214
    | exact resolve eq1214 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1217 : y = (M.op x y) := by
    first
    | (have i₁ := eq1091
       have i₂ := eq1211
       grind)
    | exact superpose eq1211 eq1091
    | exact resolve eq1091 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq1211
  have eq1236 : y = (M.op x y) := by
    first
    | (have i₁ := eq1217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1217
    | exact resolve eq1217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1217
  have eq1237 : x = y := by
    first
    | exact superpose eq1078 eq1236
    | exact resolve eq1236 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq1236
  have eq1239 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq24
    | exact resolve eq24 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1237
  have eq1263 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1239
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1239
    | exact resolve eq1239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1239
  have eq1270 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1098 eq1263
    | exact resolve eq1263 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq1263
  have eq1319 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1270 eq1100
    | exact resolve eq1100 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq1270
  have eq1344 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1215 eq70
    | (have j0 := eq70 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq70 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1215
  have eq1345 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1344
  have eq1374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1345 eq1319
    | exact resolve eq1319 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq1345
  have eq1375 : False := by grind
  exact eq1375

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_x_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq70 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq70
    | (have j0 := eq70 y x
       grind)
    | exact resolve eq70 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x X0)) X1) y) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq453 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq453 (M.op X0 X1)
       grind)
    | exact superpose eq453 eq58
    | exact resolve eq58 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq453
  have eq877 : (M.op x y) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq217 sF0 sF0
       have i₂ := eq461 x sF0
       grind)
    | exact superpose eq461 eq217
    | exact resolve eq217 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1088 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq223 sF4 sF4
       have i₂ := eq461 sF2 sF4
       grind)
    | exact superpose eq461 eq223
    | exact resolve eq223 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq461
  have eq1122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1122
    | exact resolve eq1122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1126 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1123
       have r₂ := eq27
       grind)
    | exact resolve eq1123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1128 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1126
    | exact resolve eq1126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1128
    | exact resolve eq1128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1149 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1130 eq51
    | (have r₁ := eq51
       have r₂ := eq1130
       grind)
    | exact resolve eq51 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1130
  have eq1164 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1149
  have eq1166 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1164
       have r₂ := eq85
       grind)
    | exact resolve eq1164 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1164
  have eq1170 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1166 eq83
    | exact resolve eq83 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1166
  have eq1177 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1170
    | exact resolve eq1170 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1170
  have eq1180 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1177
       have r₂ := eq84
       grind)
    | exact resolve eq1177 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1177
  have eq1182 : y = (k y x) := by
    first
    | (have r₁ := eq1180
       have r₂ := eq50
       grind)
    | exact resolve eq1180 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1180
  have eq1184 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq1182
       grind)
    | exact superpose eq1182 eq76
    | exact resolve eq76 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1185 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1182
       grind)
    | exact superpose eq1182 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1186 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1185
  have eq1188 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1186
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1186
    | exact resolve eq1186 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1189 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1184
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1184
    | exact resolve eq1184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1191 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1188
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1188
    | exact resolve eq1188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1213 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1189 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1214 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1213
  have eq1216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1214
    | exact resolve eq1214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1219 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1216
    | exact resolve eq1216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1221 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1191 eq20
    | exact resolve eq20 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1255 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1221
    | exact resolve eq1221 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1273 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1219 eq27
    | exact resolve eq27 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1255 eq1273
    | (have r₁ := eq1273
       have r₂ := eq1255
       grind)
    | exact resolve eq1273 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1341
  have eq1368 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1342 eq221
    | exact resolve eq221 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1378 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1342 eq1088
    | exact resolve eq1088 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1383 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1378
    | exact resolve eq1378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1475 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1342 eq1383
    | exact resolve eq1383 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq1383
  have eq1492 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1475
  have eq2915 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1492 eq1368
    | exact resolve eq1368 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq1492
  have eq2932 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2915
  have eq2933 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2932
    | exact resolve eq2932 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2932
  have eq2935 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2933 eq27
    | exact resolve eq27 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq2980 : x = (M.op x y) := by
    first
    | (have r₁ := eq2935
       have r₂ := eq1255
       grind)
    | exact resolve eq2935 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq2935
  have eq2982 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2980 eq20
    | exact resolve eq20 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3012 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2980 eq877
    | exact resolve eq877 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq3016 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3012
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3012
    | exact resolve eq3012 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq3028 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2982
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2982
    | exact resolve eq2982 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq3030 : x = (M.op x x) := by
    first
    | exact superpose eq2980 eq3016
    | exact resolve eq3016 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3085 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq3030
       grind)
    | exact superpose eq3030 eq56
    | exact resolve eq56 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3125 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq2980 eq3085
    | exact resolve eq3085 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq3135 : y = (M.op x y) := by
    first
    | (have i₁ := eq3125
       have i₂ := eq3030
       grind)
    | exact superpose eq3030 eq3125
    | exact resolve eq3125 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030 eq3125
  have eq3136 : y = (M.op x y) := by
    first
    | (have i₁ := eq3135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3135
    | exact resolve eq3135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3135
  have eq3137 : x = y := by
    first
    | exact superpose eq2980 eq3136
    | exact resolve eq3136 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980 eq3136
  have eq3139 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3137
       grind)
    | exact superpose eq3137 eq24
    | exact resolve eq24 eq3137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3137
  have eq3195 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3139
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3139
    | exact resolve eq3139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3139
  have eq3209 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3028 eq3195
    | exact resolve eq3195 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3209 eq1273
    | (have r₁ := eq1273
       have r₂ := eq3209
       grind)
    | exact resolve eq1273 eq3209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273 eq3209
  have eq3241 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3236
  have eq3243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3028 eq3241
    | exact resolve eq3241 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq3241
  have eq3261 : False := by grind
  exact eq3261

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq99 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq9
    | exact resolve eq9 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq136 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq158 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq136 X0 X1
       grind)
    | exact resolve eq12 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq167 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq168 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq168 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq168
    | (have j0 := eq168 X0
       grind)
    | exact resolve eq168 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq168
  have eq184 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq183
    | (have j0 := eq183 X0
       grind)
    | exact resolve eq183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq185 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq184 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq184 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq188 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq185 (σ X0)
       grind)
    | exact superpose eq185 eq15
    | exact resolve eq15 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq188
    | exact resolve eq188 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq312 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2201 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2276 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2201 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2201
    | (have j0 := eq2201 X0 X1
       grind)
    | exact resolve eq2201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq312
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq312
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq312
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq312
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq312 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2955 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq2954
  have eq36797 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2955
       grind)
    | exact superpose eq2955 eq16
    | exact resolve eq16 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq36798 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq36797
       have r₂ := eq199 x
       grind)
    | exact resolve eq36797 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36797
  have eq38114 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq167 y x
       have i₂ := eq36798
       grind)
    | exact superpose eq36798 eq167
    | exact resolve eq167 eq36798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36798
  have eq82599 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq312
       have i₂ := eq38114
       grind)
    | exact superpose eq38114 eq312
    | exact resolve eq312 eq38114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq38114
  have eq82625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq82599
  have eq82626 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq82625
  have eq82628 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq82626
       grind)
    | exact superpose eq82626 eq10
    | exact resolve eq10 eq82626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82626
  have eq82797 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq82628
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq82628
    | exact resolve eq82628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82628
  have eq83141 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82797
       grind)
    | exact superpose eq82797 eq16
    | exact resolve eq16 eq82797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82797
  have eq83142 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq83141
       have r₂ := eq199 x
       grind)
    | exact resolve eq83141 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq83141
  have eq83247 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq167 (σ y) (σ x)
       have i₂ := eq83142
       grind)
    | exact superpose eq83142 eq167
    | exact resolve eq167 eq83142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83142
  have eq83341 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq83247
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq83247
    | exact resolve eq83247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83247
  have eq83725 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83341
       grind)
    | exact superpose eq83341 eq16
    | exact resolve eq16 eq83341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83341
  have eq83942 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq83725
       have i₂ := eq2276 y x
       grind)
    | exact superpose eq2276 eq83725
    | (have j1 := eq2276 x y
       grind)
    | (have r₁ := eq83725
       have r₂ := eq2276 y x
       grind)
    | (have r₁ := eq83725
       have r₂ := eq2276 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq83725
       have r₂ := eq2276 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq83725 eq2276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq83943 : x = y ∨ x = (M.op y x) := by grind
  clear eq83942
  have eq84277 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq83725
       have i₂ := eq83943
       grind)
    | exact superpose eq83943 eq83725
    | exact resolve eq83725 eq83943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83943
  have eq84278 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq84277
       have i₂ := eq185 x
       grind)
    | exact superpose eq185 eq84277
    | exact resolve eq84277 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq84277
  have eq84279 : x = (M.op y x) := by grind
  clear eq84278
  have eq84338 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq167 y x
       have i₂ := eq84279
       grind)
    | exact superpose eq84279 eq167
    | exact resolve eq167 eq84279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq84279
  have eq85472 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq83725
       have i₂ := eq84338
       grind)
    | exact superpose eq84338 eq83725
    | exact resolve eq83725 eq84338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83725 eq84338
  have eq85491 : False := by grind
  exact eq85491

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq446 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq638 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq65 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq649 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq650 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq655 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq656 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq655 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq6456 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq656 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq656
    | (have j0 := eq656 X0 y
       grind)
    | exact resolve eq656 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq19484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19484
    | exact resolve eq19484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19484
  have eq19496 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19485
       have r₂ := eq28
       grind)
    | exact resolve eq19485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19485
  have eq19498 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19496
    | exact resolve eq19496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19496
  have eq19500 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19498 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19498
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19498
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19498
       grind)
    | exact resolve eq12 eq19498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498
  have eq19541 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq19500
  have eq19546 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19541
       have r₂ := eq27
       grind)
    | exact resolve eq19541 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19541
  have eq19653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19546 eq73
    | exact resolve eq73 eq19546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19546
  have eq19662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq19653
  have eq19665 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19662
       have r₂ := eq28
       grind)
    | exact resolve eq19662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19662
  have eq19671 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19665 eq446
    | exact resolve eq446 eq19665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19672 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq19665
  have eq19717 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19671
    | exact resolve eq19671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19671
  have eq19719 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19717
       grind)
    | exact superpose eq19717 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19717
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19717
       grind)
    | exact resolve eq12 eq19717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19717
  have eq19760 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19719
  have eq19765 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19760
       have r₂ := eq19
       grind)
    | exact resolve eq19760 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19760
  have eq19870 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19765
       grind)
    | exact superpose eq19765 eq45
    | exact resolve eq45 eq19765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19765
  have eq19890 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19870
    | exact resolve eq19870 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19870
  have eq19951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19890 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq19890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19951
    | exact resolve eq19951 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19951
  have eq19965 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19954
       have r₂ := eq28
       grind)
    | exact resolve eq19954 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19954
  have eq19967 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19965
    | exact resolve eq19965 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19965
  have eq19976 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19672 eq73
    | exact resolve eq73 eq19672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq19672
  have eq19988 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq19976
  have eq20012 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19988
       grind)
    | exact superpose eq19988 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19988
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19988
       grind)
    | exact resolve eq12 eq19988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19988
  have eq20053 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20012
  have eq20058 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq20053
       have r₂ := eq19
       grind)
    | exact resolve eq20053 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20053
  have eq20164 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq20058
       grind)
    | exact superpose eq20058 eq45
    | exact resolve eq45 eq20058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20058
  have eq20184 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq20164
    | exact resolve eq20164 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20164
  have eq26431 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19967 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19967
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19967
       grind)
    | exact resolve eq12 eq19967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19967
  have eq26490 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26431
  have eq26498 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26490
       have r₂ := eq27
       grind)
    | exact resolve eq26490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26490
  have eq28521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26498 eq19890
    | exact resolve eq19890 eq26498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19890 eq26498
  have eq28546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq28521
  have eq28567 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28546
       have r₂ := eq28
       grind)
    | exact resolve eq28546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28546
  have eq28575 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28567 eq446
    | exact resolve eq446 eq28567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28567
  have eq28645 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28575
    | exact resolve eq28575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28575
  have eq28646 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28645
  have eq28734 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28646
  have eq28938 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq28734
       grind)
    | exact superpose eq28734 eq45
    | exact resolve eq45 eq28734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28734
  have eq28979 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28938
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28938
    | exact resolve eq28938 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28938
  have eq29297 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28979 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq28979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29312 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29297
    | exact resolve eq29297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29297
  have eq29313 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq29312
  have eq29325 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq29313
    | exact resolve eq29313 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29313
  have eq32853 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq29325 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq29325
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq29325
       grind)
    | exact resolve eq12 eq29325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29325
  have eq32918 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32853
  have eq32923 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32918
       have r₂ := eq27
       grind)
    | exact resolve eq32918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32918
  have eq33110 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32923 eq28979
    | exact resolve eq28979 eq32923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28979 eq32923
  have eq33113 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33110
  have eq33138 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33113 eq446
    | exact resolve eq446 eq33113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33113
  have eq33213 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq33138
    | exact resolve eq33138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33138
  have eq33214 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33213
  have eq33216 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq33214 eq28
    | exact resolve eq28 eq33214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq34738 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6456 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6456
    | (have j0 := eq6456 x
       grind)
    | exact resolve eq6456 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6456
  have eq34811 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq34738
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq34738
    | exact resolve eq34738 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34738
  have eq34828 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq34811
    | exact resolve eq34811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq34811
  have eq34834 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq33214 eq34828
    | exact resolve eq34828 eq33214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33214 eq34828
  have eq34846 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq34834 eq60
    | exact resolve eq60 eq34834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34834
  have eq34901 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq30 eq34846
    | exact resolve eq34846 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34846
  have eq34912 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq34901
  have eq35004 : (τ (σ y)) = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq34912 eq60
    | exact resolve eq60 eq34912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq34912
  have eq35056 : y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq30 eq35004
    | exact resolve eq35004 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35004
  have eq35057 : y = (k x y) := by grind
  clear eq35056
  have eq35251 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq35057
       grind)
    | exact superpose eq35057 eq45
    | exact resolve eq45 eq35057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq35057
  have eq35293 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35251
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35251
    | exact resolve eq35251 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35251
  have eq35333 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35293 eq20184
    | exact resolve eq20184 eq35293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20184 eq35293
  have eq35342 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq35333
  have eq35348 : x = (M.op y y) := by
    first
    | (have r₁ := eq35342
       have r₂ := eq33216
       grind)
    | exact resolve eq35342 eq33216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35342
  have eq35375 : y = (M.op x y) := by
    first
    | (have i₁ := eq446 y
       have i₂ := eq35348
       grind)
    | exact superpose eq35348 eq446
    | exact resolve eq446 eq35348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq35348
  have eq35450 : y = (M.op x y) := by
    first
    | (have i₁ := eq35375
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35375
    | exact resolve eq35375 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq35375
  have eq35452 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq35450 eq21
    | exact resolve eq21 eq35450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq35450
  have eq35675 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq35452
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35452
    | exact resolve eq35452 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq35452
  have eq35689 : False := by grind
  exact eq35689

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq134 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq134 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq137
  have eq1127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1563 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1127 (σ X0) (σ X1)
       grind)
    | exact superpose eq1127 eq15
    | exact resolve eq15 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1576 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1563 X0 X1
       have i₂ := eq1127 X0 X1
       grind)
    | exact superpose eq1127 eq1563
    | exact resolve eq1563 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq1563
  have eq1588 : False := by grind
  exact eq1588

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq76 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq209 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq244 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq387 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq380 (M.op X0 X1)
       grind)
    | exact superpose eq380 eq56
    | exact resolve eq56 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq966 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq387
    | exact resolve eq387 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq387
    | exact resolve eq387 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq971 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq387
    | exact resolve eq387 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq1074 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op sF2 x)
       have i₂ := eq966 sF2 x
       grind)
    | exact superpose eq966 eq55
    | exact resolve eq55 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq6502 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq76
    | (have j0 := eq76 x
       grind)
    | exact resolve eq76 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq6524 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6502
  have eq6528 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6524
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6524
    | exact resolve eq6524 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6524
  have eq8218 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq244
    | exact resolve eq244 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq8414 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8218 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq8218
    | (have j0 := eq8218 X0 X1
       grind)
    | exact resolve eq8218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8218
  have eq29931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq29931
    | exact resolve eq29931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29931
  have eq29952 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq29941
       have r₂ := eq28
       grind)
    | exact resolve eq29941 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29941
  have eq29955 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29952 eq14
    | exact resolve eq14 eq29952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29986 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29952 eq452
    | exact resolve eq452 eq29952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq30001 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29952 eq966
    | exact resolve eq966 eq29952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30030 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq29955 x
       have i₂ := eq966 sF3 x
       grind)
    | exact superpose eq966 eq29955
    | exact resolve eq29955 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29955
  have eq199704 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30001 eq30030
    | exact resolve eq30030 eq30001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30001 eq30030
  have eq199930 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq199704
  have eq200113 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq199930 eq380
    | exact resolve eq380 eq199930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199930
  have eq200206 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq200113
  have eq200218 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq200206 eq29952
    | exact resolve eq29952 eq200206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29952
  have eq200219 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq200206 eq29986
    | exact resolve eq29986 eq200206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29986
  have eq200359 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq200219
  have eq200360 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq200218
  have eq200366 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq200359
    | exact resolve eq200359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200359
  have eq200590 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq200360
  have eq202920 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq200366 eq966
    | exact resolve eq966 eq200366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200366
  have eq202955 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq202920
    | exact resolve eq202920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202920
  have eq202956 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq202955
  have eq203041 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq202956
       grind)
    | exact superpose eq202956 eq14
    | exact resolve eq14 eq202956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203087 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq966 y x
       have i₂ := eq202956
       grind)
    | exact superpose eq202956 eq966
    | exact resolve eq966 eq202956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203222 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq203041 X0
       have i₂ := eq966 y X0
       grind)
    | exact superpose eq966 eq203041
    | exact resolve eq203041 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203041
  have eq206028 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq203222 y
       have i₂ := eq203087
       grind)
    | exact superpose eq203087 eq203222
    | exact resolve eq203222 eq203087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203087
  have eq206333 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq206028
  have eq206497 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq380 x
       have i₂ := eq206333
       grind)
    | exact superpose eq206333 eq380
    | exact resolve eq380 eq206333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206333
  have eq206593 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq206497
  have eq206699 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq202956
       have i₂ := eq206593
       grind)
    | exact superpose eq206593 eq202956
    | exact resolve eq202956 eq206593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202956
  have eq206730 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq203222 x
       have i₂ := eq206593
       grind)
    | exact superpose eq206593 eq203222
    | exact resolve eq203222 eq206593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203222 eq206593
  have eq206803 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq206730
  have eq206834 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq206699
  have eq207069 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq206834
       grind)
    | exact superpose eq206834 eq88
    | exact resolve eq88 eq206834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206834
  have eq207299 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq207069
  have eq207311 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq207299
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq207299
    | exact resolve eq207299 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207299
  have eq210533 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq207311 eq50
    | exact resolve eq50 eq207311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207311
  have eq210595 : y = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq210533
    | exact resolve eq210533 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210533
  have eq210640 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8414 x x
       have i₂ := eq210595
       grind)
    | exact superpose eq210595 eq8414
    | (have j0 := eq8414 x x
       grind)
    | exact resolve eq8414 eq210595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414 eq210595
  have eq210641 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq210640
  have eq210660 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq210641
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq210641
    | exact resolve eq210641 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210641
  have eq212866 : x ≠ y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq206803
  have eq297291 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq210660
       have r₂ := eq212866
       grind)
    | exact resolve eq210660 eq212866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210660 eq212866
  have eq297313 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq297291
       grind)
    | exact superpose eq297291 eq88
    | exact resolve eq88 eq297291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq297291
  have eq297451 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq297313
  have eq297487 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6528 eq297451
    | exact resolve eq297451 eq6528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528 eq297451
  have eq353147 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq297487 eq966
    | exact resolve eq966 eq297487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297487
  have eq353192 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq353147
    | exact resolve eq353147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353147
  have eq353193 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq353192
  have eq353429 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq353193 eq52
    | exact resolve eq52 eq353193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353452 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq353193 eq1074
    | exact resolve eq1074 eq353193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353193
  have eq353738 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq971 eq353452
    | exact resolve eq353452 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353452
  have eq354071 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq353738 eq353429
    | exact resolve eq353429 eq353738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353429 eq353738
  have eq354159 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq354071
  have eq354166 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq354159
    | exact resolve eq354159 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354159
  have eq354167 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq354166
  have eq354349 : (k x x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq356272 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq354349
       grind)
    | exact superpose eq354349 eq44
    | exact resolve eq44 eq354349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq354349
  have eq357399 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq356272
       have i₂ := eq354167
       grind)
    | exact superpose eq354167 eq356272
    | exact resolve eq356272 eq354167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354167 eq356272
  have eq357543 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq357399
  have eq357568 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq357543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq357543
    | exact resolve eq357543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357543
  have eq359092 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq357568 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq357568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357568
  have eq359114 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq359092
  have eq359214 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq359114 eq52
    | exact resolve eq52 eq359114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq359237 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq359114 eq1074
    | exact resolve eq1074 eq359114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq359114
  have eq359527 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq971 eq359237
    | exact resolve eq359237 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq359237
  have eq361648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq359527 eq359214
    | exact resolve eq359214 eq359527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359214 eq359527
  have eq361739 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq361648
  have eq361747 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq361739
    | exact resolve eq361739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361739
  have eq361748 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq361747
  have eq361917 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq361748 eq28
    | exact resolve eq28 eq361748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq797522 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq200590 eq98
    | exact resolve eq98 eq200590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq200590
  have eq797680 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq797522
  have eq797706 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq797680 eq200206
    | exact resolve eq200206 eq797680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200206 eq797680
  have eq798027 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq797706
  have eq798343 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq798027
       grind)
    | exact superpose eq798027 eq14
    | exact resolve eq14 eq798027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798389 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq966 y x
       have i₂ := eq798027
       grind)
    | exact superpose eq798027 eq966
    | exact resolve eq966 eq798027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798656 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq798343 X0
       have i₂ := eq966 y X0
       grind)
    | exact superpose eq966 eq798343
    | exact resolve eq798343 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798343
  have eq802534 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq798656 y
       have i₂ := eq798389
       grind)
    | exact superpose eq798389 eq798656
    | exact resolve eq798656 eq798389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798389 eq798656
  have eq803446 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq802534
  have eq804025 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq380 x
       have i₂ := eq803446
       grind)
    | exact superpose eq803446 eq380
    | exact resolve eq380 eq803446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq803446
  have eq804268 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq804025
  have eq804395 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq798027
       have i₂ := eq804268
       grind)
    | exact superpose eq804268 eq798027
    | exact resolve eq798027 eq804268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798027 eq804268
  have eq804657 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq804395
  have eq805031 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq966 x x
       have i₂ := eq804657
       grind)
    | exact superpose eq804657 eq966
    | exact resolve eq966 eq804657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq804657
  have eq805227 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq805031
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq805031
    | exact resolve eq805031 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805031
  have eq805252 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq805227 eq30
    | exact resolve eq30 eq805227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq805227
  have eq806856 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq805252
    | exact resolve eq805252 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805252
  have eq806857 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq806856
  have eq806892 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq806857 eq29
    | exact resolve eq29 eq806857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806857
  have eq807794 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq806892
    | exact resolve eq806892 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq806892
  have eq807824 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq807794 eq21
    | exact resolve eq21 eq807794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807794
  have eq808763 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq807824
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq807824
    | exact resolve eq807824 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807824
  have eq808766 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq808763
       have r₂ := eq361917
       grind)
    | exact resolve eq808763 eq361917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808763
  have eq808819 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq808766 eq209
    | exact resolve eq209 eq808766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq808872 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq808766 eq969
    | exact resolve eq969 eq808766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq812086 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq808819
       have i₂ := eq808872
       grind)
    | exact superpose eq808872 eq808819
    | exact resolve eq808819 eq808872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808819 eq808872
  have eq812342 : y = (M.op x y) ∨ x = y := by grind
  clear eq812086
  have eq812364 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq812342
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq812342
    | exact resolve eq812342 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812342
  have eq813112 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq812364 eq808766
    | exact resolve eq808766 eq812364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808766 eq812364
  have eq813115 : x = y := by grind
  clear eq813112
  have eq813311 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq813115
       grind)
    | exact superpose eq813115 eq19
    | exact resolve eq19 eq813115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq813312 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq813115
       grind)
    | exact superpose eq813115 eq25
    | exact resolve eq25 eq813115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq813115
  have eq814310 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq813312
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq813312
    | exact resolve eq813312 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813312
  have eq814313 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq814310 eq27
    | exact resolve eq27 eq814310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq814924 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq814310 eq361917
    | exact resolve eq361917 eq814310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361917
  have eq815598 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq361748 eq814313
    | exact resolve eq814313 eq361748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361748 eq814313
  have eq815902 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq814310 eq815598
    | exact resolve eq815598 eq814310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814310 eq815598
  have eq817318 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by grind
  have eq817658 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq815902 eq817318
    | exact resolve eq817318 eq815902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815902 eq817318
  have eq818319 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq817658 eq50
    | exact resolve eq50 eq817658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq817658
  have eq818485 : x = (k x x) := by
    first
    | exact superpose eq29 eq818319
    | exact resolve eq818319 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq818319
  have eq818604 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq818485
       grind)
    | exact superpose eq818485 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq818485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818485
  have eq818626 : x = (M.op x x) := by grind
  clear eq818604
  have eq818652 : x = (M.op x y) := by
    first
    | (have i₁ := eq818626
       have i₂ := eq813311
       grind)
    | exact superpose eq813311 eq818626
    | exact resolve eq818626 eq813311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813311 eq818626
  have eq818799 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq818652 eq21
    | exact resolve eq21 eq818652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq818652
  have eq819870 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq818799
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq818799
    | exact resolve eq818799 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq818799
  have eq820061 : False := by grind
  exact eq820061
