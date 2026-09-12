import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X1) (σ X0)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq22
    | exact resolve eq22 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq87 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq87
    | exact resolve eq87 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq87
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq195 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) x
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq24
    | exact resolve eq24 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq168
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq168
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq168 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq168
  have eq691 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq690
  have eq3775 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq24
    | exact resolve eq24 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3783 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq109 x x y
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq109
    | exact resolve eq109 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq31872 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3775 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq3775
    | exact resolve eq3775 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq32228 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq196 y (σ x)
       have i₂ := eq31872
       grind)
    | exact superpose eq31872 eq196
    | exact resolve eq196 eq31872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32629 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq32228
       grind)
    | exact superpose eq32228 eq109
    | exact resolve eq109 eq32228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq32228
  have eq32678 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32629
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq32629
    | exact resolve eq32629 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32629
  have eq33007 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (σ x) (σ y)
       have i₂ := eq32678
       grind)
    | exact superpose eq32678 eq23
    | exact resolve eq23 eq32678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32678
  have eq34181 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq33007 (σ y)
       have i₂ := eq31872
       grind)
    | exact superpose eq31872 eq33007
    | exact resolve eq33007 eq31872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31872 eq33007
  have eq34254 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq34181
  have eq34270 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34254
       have i₂ := eq195 y (σ x)
       grind)
    | exact superpose eq195 eq34254
    | exact resolve eq34254 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34254
  have eq34602 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq195 y X0
       have i₂ := eq34270
       grind)
    | exact superpose eq34270 eq195
    | exact resolve eq195 eq34270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36980 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34602 (σ y)
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq34602
    | exact resolve eq34602 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34602
  have eq40045 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36980
       have i₂ := eq34270
       grind)
    | exact superpose eq34270 eq36980
    | exact resolve eq36980 eq34270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34270 eq36980
  have eq40106 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq40045
  have eq40125 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40106
       have i₂ := eq98 (M.op x y)
       grind)
    | exact superpose eq98 eq40106
    | exact resolve eq40106 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40106
  have eq40513 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40125
       grind)
    | exact superpose eq40125 eq10
    | exact resolve eq10 eq40125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40125
  have eq40738 : x = y ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40513
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40513
    | exact resolve eq40513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40513
  have eq41078 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40738
       grind)
    | exact superpose eq40738 eq16
    | exact resolve eq16 eq40738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40738
  have eq41079 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq41078
       have r₂ := eq98 x
       grind)
    | exact resolve eq41078 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41078
  have eq41488 : (M.op (M.op x y) (M.op x y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq41079
       grind)
    | exact superpose eq41079 eq10
    | exact resolve eq10 eq41079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41505 : (τ (M.op (σ y) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq95 (M.op (M.op x y) (M.op x y))
       have i₂ := eq41079
       grind)
    | exact superpose eq41079 eq95
    | exact resolve eq95 eq41079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41724 : (M.op x y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq41505
       have i₂ := eq9 (M.op x y) x y (M.op x y)
       grind)
    | exact superpose eq9 eq41505
    | exact resolve eq41505 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41505
  have eq41737 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41488
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq41488
    | exact resolve eq41488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41488
  have eq41739 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq41724
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq41724
    | exact resolve eq41724 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq41724
  have eq94679 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3783 (M.op x x)
       have i₂ := eq23 x x y
       grind)
    | exact superpose eq23 eq3783
    | exact resolve eq3783 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq94801 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq195 x (σ y)
       have i₂ := eq94679
       grind)
    | exact superpose eq94679 eq195
    | exact resolve eq195 eq94679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq96024 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ x) (σ y) (σ (M.op x x))
       have i₂ := eq94801
       grind)
    | exact superpose eq94801 eq24
    | exact resolve eq24 eq94801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq94801
  have eq96153 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96024
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq96024
    | exact resolve eq96024 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96024
  have eq96215 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) (σ y) X0
       have i₂ := eq96153
       grind)
    | exact superpose eq96153 eq23
    | exact resolve eq23 eq96153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96153
  have eq96362 : ∀ X0 : G, y = (M.op (M.op x x) (M.op x x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq41737
       have i₂ := eq96215 X0
       grind)
    | exact superpose eq96215 eq41737
    | (have j1 := eq96215 X0
       grind)
    | exact resolve eq41737 eq96215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41737 eq96215
  have eq96470 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq96362 X0
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq96362 X0
       have i₂ := eq23 X0 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq96362
    | (have j0 := eq96362 X0
       grind)
    | exact resolve eq96362 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96362
  have eq97173 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq96470 X0
       grind)
    | exact superpose eq96470 eq16
    | (have j1 := eq96470 X0
       grind)
    | exact resolve eq16 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96470
  have eq97216 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq97173 X0
       grind)
    | (have r₁ := eq97173 X0
       have r₂ := eq98 x
       grind)
    | exact resolve eq97173 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97173
  have eq97941 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq97216 (σ x)
       have i₂ := eq94679
       grind)
    | exact superpose eq94679 eq97216
    | exact resolve eq97216 eq94679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94679
  have eq97958 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq197 x (M.op (σ y) x)
       have i₂ := eq97216 x
       grind)
    | exact superpose eq97216 eq197
    | exact resolve eq197 eq97216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq97216
  have eq98086 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97941
       have i₂ := eq196 x (σ y)
       grind)
    | exact superpose eq196 eq97941
    | exact resolve eq97941 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq97941
  have eq98104 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97958
       grind)
    | exact superpose eq97958 eq16
    | exact resolve eq16 eq97958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97958
  have eq98436 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41079
       have i₂ := eq98086
       grind)
    | exact superpose eq98086 eq41079
    | exact resolve eq41079 eq98086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41079 eq98086
  have eq98576 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98436
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq98436
       have i₂ := eq23 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq98436
    | exact resolve eq98436 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq98436
  have eq98577 : (σ x) = (σ y) := by grind
  clear eq98576
  have eq98624 : (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq98577
       grind)
    | exact superpose eq98577 eq98
    | exact resolve eq98 eq98577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98577
  have eq99026 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq98624
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq98624
    | exact resolve eq98624 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq98624
  have eq99042 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq99026
       have i₂ := eq41739
       grind)
    | exact superpose eq41739 eq99026
    | exact resolve eq99026 eq41739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41739 eq99026
  have eq99043 : False := by grind
  exact eq99043

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq288 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq289 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq293 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq289 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq302 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq293
    | (have j0 := eq293 X0 X1
       grind)
    | exact resolve eq293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq303 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq308 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq303
    | exact resolve eq303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq303 x y
       grind)
    | exact superpose eq303 eq16
    | exact resolve eq16 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq397 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq308 X0 (τ X1)
       grind)
    | exact superpose eq308 eq17
    | exact resolve eq17 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq308
  have eq413 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq397
    | exact resolve eq397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq420 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq413
    | exact resolve eq413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq432 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq319
       have i₂ := eq420 x y
       grind)
    | exact superpose eq420 eq319
    | exact resolve eq319 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq420
  have eq433 : False := by grind
  exact eq433

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) (τ X0) X1
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq19
    | exact resolve eq19 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) X2)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq19 (σ X0) (σ X1) x
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq19
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq19 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq290 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq291 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq295 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq291
    | (have j0 := eq291 X0 X1
       grind)
    | exact resolve eq291 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq304 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq1310 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | (have j0 := eq304 (τ X0) X1
       grind)
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq1389 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1310 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1310
    | (have j0 := eq1310 X0 X1
       grind)
    | exact resolve eq1310 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1400 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1389 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq1389 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq1389 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1411 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1400 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq1400
    | (have j0 := eq1400 X0 X1
       grind)
    | exact resolve eq1400 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1400
  have eq1414 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1411 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1411
    | (have j0 := eq1411 X0 X1
       grind)
    | exact resolve eq1411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1411
  have eq1526 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1414 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1414
    | exact resolve eq1414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1668 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1526 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1812 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1668 (M.op (τ X0) X1) (τ (M.op X0 X0))
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq1668
    | exact resolve eq1668 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq1668
  have eq1828 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1812 X0 X1
       have i₂ := eq116 (M.op X0 X0)
       grind)
    | exact superpose eq116 eq1812
    | (have j0 := eq1812 X0 X1
       grind)
    | exact resolve eq1812 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1812
  have eq1838 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1828
    | (have j0 := eq1828 X0 X1
       grind)
    | exact resolve eq1828 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1839 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1866 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1839 (σ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1839
    | exact resolve eq1839 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1839
  have eq1877 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1866 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1866
    | exact resolve eq1866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1886 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1877
    | exact resolve eq1877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq1990 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1886 (M.op X1 X0) (M.op X0 x)
       have i₂ := eq19 X1 X0 x
       grind)
    | exact superpose eq19 eq1886
    | exact resolve eq1886 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1886
  have eq2479 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1990 (σ X1) (σ X0)
       have i₂ := eq269 X0 X1 (σ X1)
       grind)
    | exact superpose eq269 eq1990
    | (have j1 := eq269 X0 X1 x
       grind)
    | exact resolve eq1990 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq1990
  have eq2497 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2479 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2479 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq2479 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2497 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2497
    | (have j0 := eq2497 X0 X1
       grind)
    | exact resolve eq2497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq2511 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2510 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2690 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2511 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2511
    | exact resolve eq2511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2706 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2511 x y
       grind)
    | exact superpose eq2511 eq16
    | exact resolve eq16 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2988 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2690 X0 (τ X1)
       grind)
    | exact superpose eq2690 eq17
    | exact resolve eq17 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2690
  have eq3054 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2988 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2988
    | exact resolve eq2988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3083 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3054 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3054
    | exact resolve eq3054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054
  have eq3218 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2706
       have i₂ := eq3083 x y
       grind)
    | exact superpose eq3083 eq2706
    | exact resolve eq2706 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706 eq3083
  have eq3219 : False := by grind
  exact eq3219

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyx_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq86
    | (have j0 := eq86 (σ X0) (σ X1)
       grind)
    | exact resolve eq86 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq78
    | (have j1 := eq86 y x
       grind)
    | exact resolve eq78 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op x x) (M.op X0 x)
       have i₂ := eq52 X0 x x
       grind)
    | exact superpose eq52 eq13
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq86 (τ X1) X0
       grind)
    | exact superpose eq86 eq34
    | (have j1 := eq86 (τ X1) X0
       grind)
    | exact resolve eq34 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq372 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq86 X1 (τ X0)
       grind)
    | exact superpose eq86 eq38
    | (have j1 := eq86 X1 (τ X0)
       grind)
    | exact resolve eq38 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq644 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq98 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq12 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq52
    | (have j1 := eq98 X0 X1
       grind)
    | exact resolve eq52 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq657 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq644
    | (have j0 := eq644 X0 X1
       grind)
    | exact resolve eq644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq118 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq888
    | exact resolve eq888 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq892 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq889
       have r₂ := eq27
       grind)
    | exact resolve eq889 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq895 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq892 eq266
    | exact resolve eq266 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq896 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq892 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq892
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq892
       grind)
    | exact resolve eq12 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq892 eq52
    | exact resolve eq52 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq909 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq896
  have eq910 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq909
    | exact resolve eq909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1071 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq895 eq903
    | exact resolve eq903 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq903
  have eq1088 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1071
  have eq1092 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1088 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1088
       grind)
    | exact resolve eq13 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1105 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1092
  have eq1133 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1105 eq49
    | exact resolve eq49 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1137 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1133
    | exact resolve eq1133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1140 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq86 x x
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq86
    | (have j0 := eq86 x x
       grind)
    | exact resolve eq86 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1141 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq1140
  have eq1145 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq265 y
       have i₂ := eq1141
       grind)
    | exact superpose eq1141 eq265
    | exact resolve eq265 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq1141
       grind)
    | exact superpose eq1141 eq52
    | exact resolve eq52 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1480 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1145 eq1153
    | exact resolve eq1153 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq1153
  have eq1498 : x = (M.op x x) := by grind
  clear eq1480
  have eq1500 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq265 x
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq265
    | exact resolve eq265 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq1501 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1498
       grind)
    | exact resolve eq13 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1515 : x = (k x x) := by grind
  clear eq1501
  have eq1519 : x ≠ x ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1500 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1500
       grind)
    | exact resolve eq13 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533 : x = (k (M.op x y) x) := by grind
  clear eq1519
  have eq1536 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1515
       grind)
    | exact superpose eq1515 eq43
    | exact resolve eq43 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1540 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1536
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1536
    | exact resolve eq1536 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1542 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1533 eq130
    | exact resolve eq130 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1544 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1542
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1542
    | exact resolve eq1542 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1547 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1540 eq86
    | (have j0 := eq86 (σ x) (σ x)
       grind)
    | exact resolve eq86 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1547
  have eq1551 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq86 sF1 sF2
       grind)
    | exact superpose eq86 eq1544
    | (have j1 := eq86 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1544 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1548 eq52
    | exact resolve eq52 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1748 : ∀ X0 : G, x ≠ x ∨ x = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq277 x x x
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq277
    | (have r₁ := eq277 x x x
       have r₂ := eq1498
       grind)
    | exact resolve eq277 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq1772 : ∀ X0 : G, x = (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq1748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq3188 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq910 eq85
    | exact resolve eq85 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq3192 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq3188
    | exact resolve eq3188 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3188
  have eq3928 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (M.op X0 (k x x))) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq49 eq349
    | exact resolve eq349 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq3976 : ∀ X0 : G, (k (k (σ x) (σ x)) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3928 X0
       have i₂ := eq1515
       grind)
    | exact superpose eq1515 eq3928
    | (have j0 := eq3928 X0
       grind)
    | exact resolve eq3928 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq3981 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1540 eq3976
    | (have j0 := eq3976 X0
       grind)
    | exact resolve eq3976 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq3983 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq35 eq3981
    | (have j0 := eq3981 X0
       grind)
    | exact resolve eq3981 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3981
  have eq3985 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3983 X0
       have i₂ := eq1515
       grind)
    | exact superpose eq1515 eq3983
    | (have j0 := eq3983 X0
       grind)
    | exact resolve eq3983 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq4104 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (M.op (k x x) X0)) ∨ (k x x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | exact superpose eq49 eq372
    | exact resolve eq372 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq372
  have eq4153 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (M.op x X0)) ∨ (k x x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | (have i₁ := eq4104 X0
       have i₂ := eq1515
       grind)
    | exact superpose eq1515 eq4104
    | (have j0 := eq4104 X0
       grind)
    | exact resolve eq4104 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4158 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (k x x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | exact superpose eq1540 eq4153
    | (have j0 := eq4153 X0
       grind)
    | exact resolve eq4153 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq4153
  have eq4160 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (k x x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | exact superpose eq39 eq4158
    | (have j0 := eq4158 X0
       grind)
    | exact resolve eq4158 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq4162 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq4160 X0
       have i₂ := eq1515
       grind)
    | exact superpose eq1515 eq4160
    | (have j0 := eq4160 X0
       grind)
    | exact resolve eq4160 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515 eq4160
  have eq4696 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq45 eq650
    | (have j0 := eq650 x (M.op x y) x
       grind)
    | exact resolve eq650 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq4736 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq4696
    | (have j0 := eq4696 X0
       grind)
    | exact resolve eq4696 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4696
  have eq4775 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq4736
    | (have j0 := eq4736 X0
       grind)
    | exact resolve eq4736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4736
  have eq4805 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4775 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4775
    | (have j0 := eq4775 X0
       grind)
    | exact resolve eq4775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq5556 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq3985 sF0
       grind)
    | exact superpose eq3985 eq45
    | (have j1 := eq3985 (M.op x y)
       grind)
    | exact resolve eq45 eq3985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3985
  have eq5624 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1500 eq5556
    | exact resolve eq5556 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500 eq5556
  have eq5897 : ∀ X0 : G, (σ (k (k X0 x) x)) = (k (σ (M.op x X0)) (σ x)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq39 (k X0 x)
       have i₂ := eq4162 X0
       grind)
    | exact superpose eq4162 eq39
    | (have j1 := eq4162 X0
       grind)
    | exact resolve eq39 eq4162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162
  have eq5940 : ∀ X0 : G, (σ (k (k X0 x) x)) = (σ (k (M.op x X0) x)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq39 eq5897
    | (have j0 := eq5897 X0
       grind)
    | exact resolve eq5897 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5897
  have eq5958 : ∀ X0 : G, (σ x) = (σ (k (k X0 x) x)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq5940 X0
       have i₂ := eq1772 X0
       grind)
    | exact superpose eq1772 eq5940
    | (have j0 := eq5940 X0
       grind)
    | exact resolve eq5940 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772 eq5940
  have eq5968 : ∀ X0 : G, (σ x) = (σ (k (k X0 x) x)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq5958 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5958
    | (have j0 := eq5958 X0
       grind)
    | exact resolve eq5958 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5958
  have eq6119 : ∀ X0 : G, (τ (σ x)) = (k (k X0 x) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16 (k (k X0 x) x)
       have i₂ := eq5968 X0
       grind)
    | exact superpose eq5968 eq16
    | (have j1 := eq5968 X0
       grind)
    | exact resolve eq16 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq6160 : ∀ X0 : G, x = (k (k X0 x) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq28 eq6119
    | (have j0 := eq6119 X0
       grind)
    | exact resolve eq6119 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6119
  have eq6183 : x = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6160 y
       have i₂ := eq3192
       grind)
    | exact superpose eq3192 eq6160
    | (have j0 := eq6160 y
       grind)
    | exact resolve eq6160 eq3192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160
  have eq6200 : x = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6183
  have eq6682 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3192
       have i₂ := eq6200
       grind)
    | exact superpose eq6200 eq3192
    | exact resolve eq3192 eq6200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq6692 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86 y x
       have i₂ := eq6200
       grind)
    | exact superpose eq6200 eq86
    | (have j0 := eq86 y x
       grind)
    | exact resolve eq86 eq6200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6200
  have eq6693 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6692
  have eq6697 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6682
  have eq6700 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6693
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6693
    | exact resolve eq6693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693
  have eq6717 : y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq6697
       grind)
    | exact superpose eq6697 eq255
    | exact resolve eq255 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6697
  have eq6882 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq6700
       grind)
    | exact superpose eq6700 eq255
    | exact resolve eq255 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq6700
  have eq7093 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6882 eq5624
    | exact resolve eq5624 eq6882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5624 eq6882
  have eq7121 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7093
  have eq7123 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7121
    | exact resolve eq7121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121
  have eq7297 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq657
    | (have j0 := eq657 x (M.op x y)
       grind)
    | exact resolve eq657 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq657
  have eq7327 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7297
    | exact resolve eq7297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7297
  have eq7380 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq130 eq7327
    | exact resolve eq7327 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq7327
  have eq7421 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1544 eq7380
    | exact resolve eq7380 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq7380
  have eq7462 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq7421
    | exact resolve eq7421 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7421
  have eq7499 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq7462
    | exact resolve eq7462 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7462
  have eq7532 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7499
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7499
    | exact resolve eq7499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7499
  have eq7564 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq7532
    | exact resolve eq7532 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7532
  have eq7586 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7564
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7564
    | exact resolve eq7564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564
  have eq9603 : (σ x) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7586
       have i₂ := eq86 sF2 sF1
       grind)
    | exact superpose eq86 eq7586
    | (have j1 := eq86 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq7586 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq7586
  have eq9604 : (σ x) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq9603
  have eq9605 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq9604
       have r₂ := eq1551
       grind)
    | exact resolve eq9604 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq9604
  have eq35421 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq9605 eq4805
    | exact resolve eq4805 eq9605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805 eq9605
  have eq35457 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq35421
  have eq35462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7123 eq35457
    | exact resolve eq35457 eq7123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123 eq35457
  have eq35501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq35462
    | exact resolve eq35462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35462
  have eq35503 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35501
       have r₂ := eq27
       grind)
    | exact resolve eq35501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35501
  have eq35512 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35503 eq1566
    | exact resolve eq1566 eq35503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq35555 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35512 eq35503
    | exact resolve eq35503 eq35512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35503 eq35512
  have eq35605 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35555
  have eq35640 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35605 eq67
    | (have r₁ := eq67
       have r₂ := eq35605
       grind)
    | exact resolve eq67 eq35605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq35605
  have eq35704 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35640
  have eq35722 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35704 eq85
    | exact resolve eq85 eq35704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq35723 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35704 eq118
    | exact resolve eq118 eq35704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq35704
  have eq35783 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq35723
  have eq35801 : x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq35722
    | exact resolve eq35722 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35722
  have eq35877 : x ≠ x ∨ x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq35783
       grind)
    | exact superpose eq35783 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq35783
       grind)
    | exact resolve eq12 eq35783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35783
  have eq35903 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq35877
  have eq35909 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35903
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35903
    | exact resolve eq35903 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35903
  have eq35910 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35909
  have eq36271 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35801
       have i₂ := eq35910
       grind)
    | exact superpose eq35910 eq35801
    | exact resolve eq35801 eq35910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35801 eq35910
  have eq36301 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq36271
  have eq36401 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36301 eq28
    | exact resolve eq28 eq36301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36301
  have eq36738 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq36401
    | exact resolve eq36401 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36401
  have eq36739 : x = (M.op x y) ∨ x = y := by grind
  clear eq36738
  have eq36742 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq36739 eq20
    | exact resolve eq20 eq36739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36861 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36739 eq6717
    | exact resolve eq6717 eq36739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717 eq36739
  have eq36907 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq36861
  have eq36923 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36907
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq36907
    | exact resolve eq36907 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36907
  have eq36924 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq36923
  have eq36985 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq36742
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36742
    | exact resolve eq36742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36742
  have eq37137 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq36924 eq27
    | exact resolve eq27 eq36924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36924
  have eq37496 : x = y := by
    first
    | (have r₁ := eq37137
       have r₂ := eq36985
       grind)
    | exact resolve eq37137 eq36985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36985 eq37137
  have eq37549 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37496
       grind)
    | exact superpose eq37496 eq18
    | exact resolve eq18 eq37496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37550 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq37496
       grind)
    | exact superpose eq37496 eq24
    | exact resolve eq24 eq37496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37496
  have eq37846 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37550
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37550
    | exact resolve eq37550 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37550
  have eq37847 : x = (M.op x y) := by
    first
    | (have i₁ := eq37549
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq37549
    | exact resolve eq37549 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq37549
  have eq37925 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37846 eq26
    | exact resolve eq26 eq37846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37846
  have eq38213 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1548 eq37925
    | exact resolve eq37925 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq37925
  have eq38292 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37847 eq20
    | exact resolve eq20 eq37847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37847
  have eq38518 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq38292
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38292
    | exact resolve eq38292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38292
  have eq38667 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq38213 eq27
    | exact resolve eq27 eq38213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq38213
  have eq39512 : False := by grind
  exact eq39512

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq61 X0 x x
       grind)
    | exact superpose eq61 eq12
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq366 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq366 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq366 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq378 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq367 (σ X0)
       grind)
    | exact superpose eq367 eq15
    | exact resolve eq15 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq367 (τ X0)
       grind)
    | exact superpose eq367 eq31
    | exact resolve eq31 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq391 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq384 X0
       have i₂ := eq367 X0
       grind)
    | exact superpose eq367 eq384
    | exact resolve eq384 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq397 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq367 X0
       grind)
    | exact superpose eq367 eq378
    | exact resolve eq378 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq378
  have eq444 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq61
    | exact resolve eq61 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) (σ X0) x
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq92
    | exact resolve eq92 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq533 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (σ X0) X1) (σ (M.op X0 X0))
       have i₂ := eq444 X0 X1
       grind)
    | exact superpose eq444 eq13
    | (have j0 := eq13 (M.op (σ X0) X1) (σ (M.op X0 X0))
       grind)
    | exact resolve eq13 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq544 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq397 (M.op X0 X0)
       grind)
    | exact superpose eq397 eq533
    | (have j0 := eq533 X0 X1
       grind)
    | exact resolve eq533 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq551 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq544 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq552 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq555 : ∀ X0 X1 : G, (k (M.op (σ X0) X1) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq397 (M.op X0 X0)
       grind)
    | exact superpose eq397 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq556 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq555 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq555
    | (have j0 := eq555 X0 X1
       grind)
    | exact resolve eq555 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq557 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq556 X0 X1
       have j1 := eq451 X0 X1
       grind)
    | (have r₁ := eq556 X0 X1
       have r₂ := eq451 X0 X1
       grind)
    | exact resolve eq556 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq556
  have eq572 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) (M.op X0 X0)
       have i₂ := eq557 X0 X1
       grind)
    | exact superpose eq557 eq22
    | exact resolve eq22 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq573 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq572
    | exact resolve eq572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq628 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq664 : ∀ X0 X1 : G, (σ X0) = (k (τ (M.op (σ (σ X0)) X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq573 (σ X0) X1
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq573
    | exact resolve eq573 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq1264 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (M.op (σ (σ X0)) X1)) (M.op X0 X0)
       have i₂ := eq664 X0 X1
       grind)
    | exact superpose eq664 eq22
    | exact resolve eq22 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq664
  have eq1267 : ∀ X0 X1 : G, (k (τ (τ (M.op (σ (σ X0)) X1))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1264
    | exact resolve eq1264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq2125 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq645 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq645
    | exact resolve eq645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq2223 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2125 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2125
    | (have j0 := eq2125 X0 X1
       grind)
    | exact resolve eq2125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2125
  have eq2236 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2223 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq2223 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq2223 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2243 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2236 X0 X1
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq2236
    | (have j0 := eq2236 X0 X1
       grind)
    | exact resolve eq2236 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2247 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2243 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2243
    | (have j0 := eq2243 X0 X1
       grind)
    | exact resolve eq2243 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2357 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2247 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2247
    | exact resolve eq2247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq3386 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq2357 (τ (M.op (σ X0) X1)) (M.op X0 X0)
       grind)
    | exact superpose eq2357 eq573
    | (have j1 := eq2357 (τ (M.op (σ X0) X1)) (M.op X0 X0)
       grind)
    | exact resolve eq573 eq2357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq3390 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (τ (M.op (σ (σ X0)) X1)))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (τ (τ (M.op (σ (σ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1267 X0 X1
       have i₂ := eq2357 (τ (τ (M.op (σ (σ X0)) X1))) (M.op X0 X0)
       grind)
    | exact superpose eq2357 eq1267
    | (have j1 := eq2357 (τ (τ (M.op (σ (σ X0)) X1))) (M.op X0 X0)
       grind)
    | exact resolve eq1267 eq2357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq2357
  have eq3413 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (τ (M.op (σ (σ X0)) X1)))) = X0 ∨ (M.op (M.op X0 X0) (τ (τ (M.op (σ (σ X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3390 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq3390 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq3390
    | (have j0 := eq3390 X0 X1
       grind)
    | exact resolve eq3390 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3414 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (τ (M.op (σ (σ X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413
  have eq3418 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3386 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq3386 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq3386
    | (have j0 := eq3386 X0 X1
       grind)
    | exact resolve eq3386 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3419 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418
  have eq3456 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3419 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3419
    | exact resolve eq3419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3508 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3456 X0 X1
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq3456
    | exact resolve eq3456 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq3456
  have eq3713 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (M.op (τ (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (τ (M.op X0 X0)) (τ (M.op X0 X1)) X2
       have i₂ := eq3508 X0 X1
       grind)
    | exact superpose eq3508 eq61
    | exact resolve eq61 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3508
  have eq4213 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (τ (M.op (σ (σ X0)) X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (τ (τ (M.op (σ (σ X0)) X1))) X1 (M.op X0 X0)
       have i₂ := eq3414 X0 X1
       grind)
    | exact superpose eq3414 eq67
    | exact resolve eq67 eq3414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3414
  have eq4789 : ∀ X0 X1 X3 : G, (τ X0) = (M.op (τ (M.op X1 X0)) (M.op (τ X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3713 (M.op x X0) (τ (τ (M.op (σ (σ X0)) X1))) x
       have i₂ := eq4213 X0 X1 x
       grind)
    | exact superpose eq4213 eq3713
    | exact resolve eq3713 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4975 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3713 X1 X0 (M.op (τ X0) x)
       have i₂ := eq4789 X0 X1 x
       grind)
    | exact superpose eq4789 eq3713
    | exact resolve eq3713 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713 eq4789
  have eq5068 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4975 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4975
    | exact resolve eq4975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4975
  have eq5356 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq5068 X0 X1
       grind)
    | exact superpose eq5068 eq11
    | exact resolve eq11 eq5068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5628 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5356 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5356
    | exact resolve eq5356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq6088 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5628 y x
       grind)
    | exact superpose eq5628 eq16
    | (have r₁ := eq16
       have r₂ := eq5628 y x
       grind)
    | exact resolve eq16 eq5628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq6202 : False := by grind
  exact eq6202

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq185 eq177
    | exact resolve eq177 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq189 eq177
    | exact resolve eq177 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq747 X0
       have i₂ := eq177 X0 X0 X0
       grind)
    | (have i₁ := eq747 X0
       have i₂ := eq177 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq177 eq747
    | (have j0 := eq747 X0
       grind)
    | exact resolve eq747 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq750 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq40
    | exact resolve eq40 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq733
  have eq751 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq750
    | exact resolve eq750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq753 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq751
    | exact resolve eq751 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq753 eq738
    | exact resolve eq738 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq770 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq763
       have r₂ := eq27
       grind)
    | exact resolve eq763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq775 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq770 eq190
    | exact resolve eq190 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq781 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq770 eq177
    | exact resolve eq177 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq775 eq186
    | exact resolve eq186 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq775
  have eq832 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq789 eq781
    | exact resolve eq781 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq789
  have eq845 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq832
  have eq850 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq845 eq13
    | exact resolve eq13 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq845 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq860 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq850
       have r₂ := eq853
       grind)
    | exact resolve eq850 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq853
  have eq862 : (τ (σ x)) = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq860 eq116
    | exact resolve eq116 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq860
  have eq869 : y = (M.op x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq862
    | exact resolve eq862 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq879 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq177
    | exact resolve eq177 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq177 x x X0
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq177
    | exact resolve eq177 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : x = (M.op y y) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq879 x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq879
    | exact resolve eq879 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k y (M.op X0 x)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq13 y (M.op X0 x)
       have i₂ := eq879 X0
       grind)
    | exact superpose eq879 eq13
    | exact resolve eq13 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq999 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq986
  have eq1021 : y = (M.op (M.op x y) x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq185 (M.op x x)
       have i₂ := eq880 x
       grind)
    | exact superpose eq880 eq185
    | exact resolve eq185 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 : G, x = (k (M.op x X0) y) ∨ (M.op y y) = (M.op x X0) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op x X0) y
       have i₂ := eq880 X0
       grind)
    | exact superpose eq880 eq28
    | (have j0 := eq28 (M.op x X0) y
       grind)
    | exact resolve eq28 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq1033 : ∀ X0 : G, x = (k (M.op x X0) y) ∨ x = (M.op x X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq999 eq1025
    | (have j0 := eq1025 X0
       grind)
    | exact resolve eq1025 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1025
  have eq1101 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 (M.op (k X0 X1) X2)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 X0 x
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1160 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq770 eq748
    | exact resolve eq748 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1165 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq748 y
       grind)
    | exact superpose eq748 eq41
    | (have j1 := eq748 y
       grind)
    | exact resolve eq41 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq1174 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq1165
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1165
    | exact resolve eq1165 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1178 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq1160
    | exact resolve eq1160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1182 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1178 eq753
    | exact resolve eq753 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq1178
  have eq1188 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1182
  have eq1201 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq189
    | exact resolve eq189 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq177
    | exact resolve eq177 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1239 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1201 eq185
    | exact resolve eq185 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1244 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1201 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1404 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1239 eq1208
    | exact resolve eq1208 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq1239
  have eq1420 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1404
  have eq1430 : x ≠ y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1420
       grind)
    | exact superpose eq1420 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1420
       grind)
    | exact resolve eq13 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1433 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq1420
       grind)
    | exact superpose eq1420 eq28
    | exact resolve eq28 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1441 : x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1430
       have r₂ := eq1433
       grind)
    | exact resolve eq1430 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430 eq1433
  have eq1444 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1441
       grind)
    | exact superpose eq1441 eq41
    | exact resolve eq41 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1447 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1444
    | exact resolve eq1444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq1449 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1447
    | exact resolve eq1447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq3146 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1244
       grind)
    | exact superpose eq1244 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1244
       grind)
    | exact resolve eq13 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3149 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq1244
       grind)
    | exact superpose eq1244 eq28
    | exact resolve eq28 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq3173 : (M.op x y) = (k y y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3146
       have r₂ := eq3149
       grind)
    | exact resolve eq3146 eq3149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146 eq3149
  have eq3604 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3173
       grind)
    | exact superpose eq3173 eq41
    | exact resolve eq41 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3620 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3604
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3604
    | exact resolve eq3604 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604
  have eq3622 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3620
    | exact resolve eq3620 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq3624 : (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1449 eq3622
    | exact resolve eq3622 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449 eq3622
  have eq3625 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3624
  have eq4893 : x ≠ y ∨ x = (k y y) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1021 eq989
    | exact resolve eq989 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq1021
  have eq4894 : x ≠ y ∨ x = (k y y) := by grind
  clear eq4893
  have eq4912 : x = (k y y) ∨ x = y ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1033 x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq1033
    | exact resolve eq1033 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq1033
  have eq4927 : x = (k y y) ∨ x = y := by grind
  clear eq4912
  have eq4938 : x = (k y y) := by
    first
    | (have r₁ := eq4927
       have r₂ := eq4894
       grind)
    | exact resolve eq4927 eq4894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4894 eq4927
  have eq4946 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq41
    | exact resolve eq41 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4949 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4946
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4946
    | exact resolve eq4946 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4946
  have eq4951 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4949
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4949
    | exact resolve eq4949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949
  have eq8684 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq708 y y X0
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq708
    | (have j0 := eq708 y y x
       grind)
    | exact resolve eq708 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8730 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq4951 eq708
    | (have j0 := eq708 (σ y) (σ y) x
       grind)
    | exact resolve eq708 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8842 : y = (M.op y y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq189 (M.op x y)
       have i₂ := eq8684 x
       grind)
    | exact superpose eq8684 eq189
    | exact resolve eq189 eq8684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8857 : ∀ X1 : G, x = (M.op y (M.op x X1)) ∨ y = (M.op y y) := by
    intro X1
    first
    | (have i₁ := eq177 (M.op x y) x X1
       have i₂ := eq8684 x
       grind)
    | exact superpose eq8684 eq177
    | exact resolve eq177 eq8684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8684
  have eq8940 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq8842
       grind)
    | exact superpose eq8842 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq8842
       grind)
    | exact resolve eq13 eq8842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8842
  have eq8963 : y = (k y y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq8940
  have eq8967 : x = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq8963
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq8963
    | exact resolve eq8963 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8963
  have eq8983 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq8967 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq8967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8967
  have eq9250 : ∀ X1 : G, (σ x) = (M.op (σ y) (M.op (σ x) X1)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X1
    first
    | exact superpose eq8730 eq177
    | exact resolve eq177 eq8730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8730
  have eq10216 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq709 y y X0
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq709
    | (have j0 := eq709 y y x
       grind)
    | exact resolve eq709 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10263 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq4951 eq709
    | (have j0 := eq709 (σ y) (σ y) x
       grind)
    | exact resolve eq709 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10890 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8857 (M.op y x)
       have i₂ := eq10216 x
       grind)
    | exact superpose eq10216 eq8857
    | exact resolve eq8857 eq10216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857 eq10216
  have eq10917 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq10890
  have eq10988 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq10917
       grind)
    | exact superpose eq10917 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq10917
       grind)
    | exact resolve eq13 eq10917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11011 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq10917
  have eq11013 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq10988
  have eq11018 : x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11013
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq11013
    | exact resolve eq11013 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4938 eq11013
  have eq11022 : x = (M.op y y) := by
    first
    | (have r₁ := eq11018
       have r₂ := eq11011
       grind)
    | exact resolve eq11018 eq11011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11011 eq11018
  have eq11033 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq185 y
       have i₂ := eq11022
       grind)
    | exact superpose eq11022 eq185
    | exact resolve eq185 eq11022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq11066 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq11022
       grind)
    | exact superpose eq11022 eq177
    | exact resolve eq177 eq11022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11067 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 y y X0
       have i₂ := eq11022
       grind)
    | exact superpose eq11022 eq177
    | exact resolve eq177 eq11022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11097 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq11033 eq189
    | exact resolve eq189 eq11033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq11110 : y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11033 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq11033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11033
  have eq11144 : x ≠ y ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq11097 eq13
    | exact resolve eq13 eq11097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11147 : x = (k (M.op x y) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq11097 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq11097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11168 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11147
       have i₂ := eq11022
       grind)
    | exact superpose eq11022 eq11147
    | exact resolve eq11147 eq11022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147
  have eq11193 : y = (M.op x x) := by
    first
    | (have i₁ := eq11066 y
       have i₂ := eq11022
       grind)
    | exact superpose eq11022 eq11066
    | exact resolve eq11066 eq11022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11022 eq11066
  have eq11353 : y = (M.op x (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq11067 y
       have i₂ := eq8983
       grind)
    | exact superpose eq8983 eq11067
    | exact resolve eq11067 eq8983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11067
  have eq11407 : y = (M.op x (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq11353
       have r₂ := eq11144
       grind)
    | exact resolve eq11353 eq11144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11353
  have eq11408 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq11168 eq11407
    | exact resolve eq11407 eq11168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11407
  have eq12647 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11110 eq42
    | exact resolve eq42 eq11110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11110
  have eq12655 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12647
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12647
    | exact resolve eq12647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647
  have eq12657 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12655
    | exact resolve eq12655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12655
  have eq12666 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq11408 eq13
    | exact resolve eq13 eq11408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12669 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq11408 eq28
    | exact resolve eq28 eq11408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11408
  have eq12693 : y = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq12666
       have r₂ := eq12669
       grind)
    | exact resolve eq12666 eq12669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12666 eq12669
  have eq12792 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq12693 eq42
    | exact resolve eq42 eq12693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12693
  have eq12797 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq20 eq12792
    | exact resolve eq12792 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12792
  have eq12799 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq12797
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12797
    | exact resolve eq12797 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12797
  have eq12843 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq10263 eq9250
    | exact resolve eq9250 eq10263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9250 eq10263
  have eq12870 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq12843
  have eq12907 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12870 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq12870
       grind)
    | exact resolve eq13 eq12870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12931 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq12870
  have eq12933 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq12907
  have eq12937 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4951 eq12933
    | exact resolve eq12933 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951 eq12933
  have eq12941 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq12937
       have r₂ := eq12931
       grind)
    | exact resolve eq12937 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12931 eq12937
  have eq12981 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq12941 eq177
    | exact resolve eq177 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12982 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq12941 eq177
    | exact resolve eq177 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq12995 : ∀ X0 : G, (σ y) = (M.op (σ x) (k X0 (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq12941 eq708
    | exact resolve eq708 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq13106 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12941 eq12981
    | exact resolve eq12981 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12981
  have eq14666 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq1174
       have i₂ := eq8983
       grind)
    | exact superpose eq8983 eq1174
    | exact resolve eq1174 eq8983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq8983
  have eq14699 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq14666
       have r₂ := eq11144
       grind)
    | exact resolve eq14666 eq11144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14666
  have eq14711 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq20 eq14699
    | exact resolve eq14699 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14699
  have eq14714 : x = y ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq11097 eq14711
    | exact resolve eq14711 eq11097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14711
  have eq14715 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq14714
       have r₂ := eq11144
       grind)
    | exact resolve eq14714 eq11144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11144 eq14714
  have eq14749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq14715 eq12995
    | (have j0 := eq12995 (σ (M.op x y))
       grind)
    | exact resolve eq12995 eq14715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12995
  have eq14750 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq14715 eq709
    | (have j0 := eq709 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq709 eq14715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14715
  have eq14753 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq12941 eq14750
    | (have j0 := eq14750 X0
       grind)
    | exact resolve eq14750 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14750
  have eq14754 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq26 eq14749
    | exact resolve eq14749 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14749
  have eq14758 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3625 eq14754
    | exact resolve eq14754 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625 eq14754
  have eq26725 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq14753 eq12982
    | exact resolve eq12982 eq14753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12982 eq14753
  have eq26781 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq14758 eq26725
    | exact resolve eq26725 eq14758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26725
  have eq26807 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq26781 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq26781
       grind)
    | exact resolve eq13 eq26781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26781
  have eq26848 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by grind
  clear eq26807
  have eq26863 : (τ (σ x)) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq26848 eq125
    | exact resolve eq125 eq26848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq26848
  have eq26888 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq30 eq26863
    | exact resolve eq26863 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26863
  have eq26894 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq11168 eq26888
    | exact resolve eq26888 eq11168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11168 eq26888
  have eq26908 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq26894 eq42
    | exact resolve eq42 eq26894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq26894
  have eq26932 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq20 eq26908
    | exact resolve eq26908 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26908
  have eq26934 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq12799 eq26932
    | exact resolve eq26932 eq12799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12799 eq26932
  have eq26936 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq14758 eq26934
    | exact resolve eq26934 eq14758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14758 eq26934
  have eq26937 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq26936
  have eq26944 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26937 eq41
    | exact resolve eq41 eq26937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq26937
  have eq26975 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq26944
    | exact resolve eq26944 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26944
  have eq26977 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26975
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26975
    | exact resolve eq26975 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26975
  have eq27000 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq26977 eq709
    | (have j0 := eq709 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq709 eq26977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq26977
  have eq27015 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq12941 eq27000
    | (have j0 := eq27000 X0
       grind)
    | exact resolve eq27000 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12941 eq27000
  have eq27016 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq27015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27015
  have eq27025 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (k X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq27016 (M.op (k X0 sF1) x)
       have i₂ := eq1101 X0 sF1 x
       grind)
    | exact superpose eq1101 eq27016
    | (have j1 := eq1101 X0 (σ (M.op x y)) x
       grind)
    | exact resolve eq27016 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq29664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12657 eq27025
    | (have j0 := eq27025 (σ x)
       grind)
    | exact resolve eq27025 eq12657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12657 eq27025
  have eq29746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq29664
    | exact resolve eq29664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29664
  have eq29749 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq29746
       have r₂ := eq27
       grind)
    | exact resolve eq29746 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29746
  have eq29755 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29749 eq27016
    | exact resolve eq27016 eq29749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27016 eq29749
  have eq29805 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq29755
  have eq29813 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13106 eq29805
    | exact resolve eq29805 eq13106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29805
  have eq29833 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29813 eq209
    | exact resolve eq209 eq29813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29813
  have eq29889 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29833
       have i₂ := eq11193
       grind)
    | exact superpose eq11193 eq29833
    | exact resolve eq29833 eq11193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29833
  have eq29892 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29889 eq29
    | exact resolve eq29 eq29889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29889
  have eq29965 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq29892
    | exact resolve eq29892 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq29892
  have eq29966 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq29965
  have eq29975 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29966 eq29
    | exact resolve eq29 eq29966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29966
  have eq30022 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq29975
    | exact resolve eq29975 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29975
  have eq30064 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30022
       grind)
    | exact superpose eq30022 eq18
    | exact resolve eq18 eq30022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30241 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11097
       have i₂ := eq30022
       grind)
    | exact superpose eq30022 eq11097
    | exact resolve eq11097 eq30022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11097
  have eq30714 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30064 eq197
    | exact resolve eq197 eq30064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq30064
  have eq30770 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30022 eq30714
    | exact resolve eq30714 eq30022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30022 eq30714
  have eq31178 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30770 eq30241
    | exact resolve eq30241 eq30770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30241 eq30770
  have eq31232 : x = (M.op x y) := by grind
  clear eq31178
  have eq31241 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31232
       grind)
    | exact superpose eq31232 eq18
    | exact resolve eq18 eq31232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31242 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31232
       grind)
    | exact superpose eq31232 eq22
    | exact resolve eq22 eq31232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq31340 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq11193
       have i₂ := eq31232
       grind)
    | exact superpose eq31232 eq11193
    | exact resolve eq11193 eq31232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11193
  have eq31387 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31242 eq20
    | exact resolve eq20 eq31242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq31572 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq31241 eq209
    | exact resolve eq209 eq31241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq31241
  have eq31641 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq31572
       have i₂ := eq31232
       grind)
    | exact superpose eq31232 eq31572
    | exact resolve eq31572 eq31232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31232 eq31572
  have eq31830 : y = (M.op x y) := by
    first
    | exact superpose eq31641 eq31340
    | exact resolve eq31340 eq31641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31340 eq31641
  have eq31893 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31830
       grind)
    | exact superpose eq31830 eq24
    | exact resolve eq24 eq31830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31830
  have eq32198 : (σ x) = (σ y) := by
    first
    | exact superpose eq31242 eq31893
    | exact resolve eq31893 eq31242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31242 eq31893
  have eq32232 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32198 eq26
    | exact resolve eq26 eq32198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq32489 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13106 eq32232
    | exact resolve eq32232 eq13106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13106 eq32232
  have eq32502 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32198 eq32489
    | exact resolve eq32489 eq32198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32198 eq32489
  have eq32508 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq32502 eq27
    | exact resolve eq27 eq32502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32502
  have eq32556 : False := by grind
  exact eq32556

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq126 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq190 : (σ (k (k y x) (M.op x y))) = (k (k (σ y) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq41
    | exact resolve eq41 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq70 (σ X0) sF1
       grind)
    | exact superpose eq70 eq41
    | (have j1 := eq70 X0 (σ (M.op x y))
       grind)
    | exact resolve eq41 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq204 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq229 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq204 eq14
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq247 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq52 X2 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq869
    | exact resolve eq869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq873 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq870
       have r₂ := eq27
       grind)
    | exact resolve eq870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq877 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq873 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq873
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq873
       grind)
    | exact resolve eq13 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq889 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq877
  have eq930 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq889 eq49
    | exact resolve eq49 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq889
  have eq934 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq930
    | exact resolve eq930 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq961 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq934
       grind)
    | exact superpose eq934 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq962 : x = (M.op x x) := by grind
  clear eq961
  have eq965 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq257 x
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq257
    | exact resolve eq257 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq966 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq962
       grind)
    | exact resolve eq12 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq962
       grind)
    | exact resolve eq13 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq979 : x = (k x x) := by grind
  clear eq967
  have eq980 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq966 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq985 : x ≠ x ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq965 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq965
       grind)
    | exact resolve eq13 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq997 : x = (k (M.op x y) x) := by grind
  clear eq985
  have eq1002 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq979
       grind)
    | exact superpose eq979 eq43
    | exact resolve eq43 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq979
  have eq1006 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1002
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1002
    | exact resolve eq1002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1008 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq997 eq126
    | exact resolve eq126 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1010 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1008
    | exact resolve eq1008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1035 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1006 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1036 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1035
  have eq1044 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq1036 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1036
       grind)
    | exact resolve eq12 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1036 eq52
    | exact resolve eq52 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1396 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) ∨ (k (M.op X0 X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq980 (M.op X0 X0)
       have i₂ := eq52 X0 X0 X0
       grind)
    | exact superpose eq52 eq980
    | (have j0 := eq980 (M.op X0 X0)
       grind)
    | exact resolve eq980 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1630 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) ∨ (k (M.op X0 X0) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1058 (M.op X0 X0)
       have i₂ := eq52 X0 X0 X0
       grind)
    | exact superpose eq52 eq1058
    | (have j0 := eq1058 (M.op X0 X0)
       grind)
    | exact resolve eq1058 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1649 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 (σ x))) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 X0
       have i₂ := eq1058 X0
       grind)
    | (have i₁ := eq52 X0 (σ x) X0
       have i₂ := eq1058 X0
       grind)
    | exact superpose eq1058 eq52
    | (have j1 := eq1058 X0
       grind)
    | exact resolve eq52 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1650 : ∀ X0 X1 : G, (M.op (k X0 (σ x)) (M.op X0 X1)) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X1
       have i₂ := eq1058 X0
       grind)
    | (have i₁ := eq52 (σ x) X0 x
       have i₂ := eq1058 X0
       grind)
    | exact superpose eq1058 eq52
    | (have j1 := eq1058 X0
       grind)
    | exact resolve eq52 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq2518 : ∀ X0 : G, (k (M.op X0 X0) x) = X0 ∨ (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq259 X0 x X0
       have i₂ := eq1396 X0
       grind)
    | exact superpose eq1396 eq259
    | (have j1 := eq1396 X0
       grind)
    | exact resolve eq259 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2519 : ∀ X0 : G, x ≠ x ∨ x = (k (M.op X0 X0) x) ∨ (k (M.op X0 X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) x
       have i₂ := eq1396 X0
       grind)
    | exact superpose eq1396 eq13
    | (have j1 := eq1396 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) x
       have r₂ := eq1396 X0
       grind)
    | exact resolve eq13 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2533 : ∀ X0 : G, x = (k (M.op X0 X0) x) ∨ (k (M.op X0 X0) x) = X0 := by
    intro X0
    first
    | (have j0 := eq2519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq3604 : ∀ X0 : G, (M.op x (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2518 (M.op x x)
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq2518
    | exact resolve eq2518 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq3652 : ∀ X0 : G, x ≠ X0 ∨ (k (M.op X0 X0) x) = X0 := by
    intro X0
    first
    | (have j0 := eq2533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq6452 : ∀ X0 : G, x = X0 ∨ (k (M.op X0 X0) x) = X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1396 X0
       have i₂ := eq3604 X0
       grind)
    | exact superpose eq3604 eq1396
    | (have j0 := eq1396 X0
       have j1 := eq3604 X0
       grind)
    | exact resolve eq1396 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396 eq3604
  have eq6472 : ∀ X0 : G, (k (M.op X0 X0) x) = X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq6452 X0
       have j1 := eq3652 X0
       grind)
    | (have r₁ := eq6452 X0
       have r₂ := eq3652 X0
       grind)
    | (have r₁ := eq6452 x
       have r₂ := eq3652 x
       grind)
    | (have r₁ := eq6452 x
       have r₂ := eq3652 (k (M.op x x) x)
       grind)
    | exact resolve eq6452 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652 eq6452
  have eq6956 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (M.op (M.op (σ x) X0) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1630 eq53
    | (have j1 := eq1630 (M.op (σ x) X0)
       grind)
    | exact resolve eq53 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6957 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq1630 eq259
    | (have j1 := eq1630 X0
       grind)
    | exact resolve eq259 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq1630
  have eq6977 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (M.op (σ x) X0) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | (have j0 := eq6956 X0
       have j1 := eq420 (σ x) X0 (M.op (σ x) X0)
       grind)
    | (have r₁ := eq6956 x
       have r₂ := eq420 (σ x) x x
       grind)
    | exact resolve eq6956 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq6956
  have eq8321 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1649
    | (have j0 := eq1649 (σ y) (σ x)
       grind)
    | exact resolve eq1649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq9152 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1010 eq1650
    | (have j0 := eq1650 (σ (M.op x y)) x
       grind)
    | exact resolve eq1650 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9173 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) X0) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq1650
    | (have j0 := eq1650 (M.op (M.op (σ x) (σ y)) X0) x
       grind)
    | exact resolve eq1650 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1650
  have eq9347 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (k (M.op (M.op (σ x) (σ y)) X0) (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq229 eq9173
    | (have j0 := eq9173 X0
       grind)
    | exact resolve eq9173 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq9173
  have eq9491 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq9152 eq1051
    | exact resolve eq1051 eq9152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq9152
  have eq9522 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq9491
  have eq9544 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq9522 eq52
    | exact resolve eq52 eq9522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9522
  have eq9560 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq199 eq9544
    | exact resolve eq9544 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq9544
  have eq9862 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (k X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9560 (τ X0)
       have i₂ := eq34 X0 sF0
       grind)
    | exact superpose eq34 eq9560
    | exact resolve eq9560 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq9560
  have eq9905 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (k X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq9862
    | (have j0 := eq9862 X0
       grind)
    | exact resolve eq9862 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9862
  have eq12112 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6957 (M.op x x)
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq6957
    | exact resolve eq6957 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq6957
  have eq13742 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq12112 eq6977
    | (have j1 := eq12112 X0
       grind)
    | exact resolve eq6977 eq12112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6977 eq12112
  have eq17799 : (k (k (σ y) (σ x)) (σ (M.op x y))) = (σ (k (M.op y y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq980 y
       grind)
    | exact superpose eq980 eq190
    | (have j1 := eq980 y
       grind)
    | exact resolve eq190 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq980
  have eq17852 : (k (k (σ y) (σ x)) (σ (M.op x y))) = (σ (k (M.op y y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17799
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17799
    | exact resolve eq17799 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17799
  have eq18831 : (k (k (σ y) (σ x)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op y y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq17852
       have i₂ := eq70 (M.op y y) sF0
       grind)
    | exact superpose eq70 eq17852
    | (have j1 := eq70 x (M.op x y)
       grind)
    | exact resolve eq17852 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq17852
  have eq18882 : (σ y) = (k (k (σ y) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq247 eq18831
    | exact resolve eq18831 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq18831
  have eq18887 : (σ y) = (k (k (σ y) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq18882
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18882
    | exact resolve eq18882 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18882
  have eq19400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18887 eq9905
    | exact resolve eq9905 eq18887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9905 eq18887
  have eq19408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq19400
    | exact resolve eq19400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19400
  have eq19411 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq19408
       have r₂ := eq27
       grind)
    | exact resolve eq19408 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19408
  have eq19445 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19411 eq13742
    | exact resolve eq13742 eq19411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13742 eq19411
  have eq19476 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq19445
  have eq19482 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1010 eq19476
    | exact resolve eq19476 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010 eq19476
  have eq19531 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19482 eq6472
    | exact resolve eq6472 eq19482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472 eq19482
  have eq19568 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq19531
  have eq19580 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq997 eq19568
    | exact resolve eq19568 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997 eq19568
  have eq19581 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq19580
  have eq19719 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19581 eq28
    | exact resolve eq28 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19581
  have eq19975 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq19719
    | exact resolve eq19719 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19719
  have eq19976 : x = (M.op x y) := by grind
  clear eq19975
  have eq19979 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19976 eq20
    | exact resolve eq20 eq19976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19983 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq19976 eq66
    | (have r₁ := eq66
       have r₂ := eq19976
       grind)
    | exact resolve eq66 eq19976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq19976
  have eq20081 : x = (k y x) := by grind
  clear eq19983
  have eq20129 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19979
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19979
    | exact resolve eq19979 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19979
  have eq20156 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20129 eq26
    | exact resolve eq26 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq20181 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20129 eq1036
    | exact resolve eq1036 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq20277 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20129 eq8321
    | exact resolve eq8321 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8321
  have eq20404 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) := by
    first
    | (have r₁ := eq20277
       have r₂ := eq27
       grind)
    | exact resolve eq20277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20277
  have eq20445 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq20081
       grind)
    | exact superpose eq20081 eq76
    | exact resolve eq76 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq20081
  have eq20495 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20129 eq20445
    | exact resolve eq20445 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20445
  have eq20508 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20495
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20495
    | exact resolve eq20495 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20495
  have eq20517 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20129 eq20508
    | exact resolve eq20508 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20508
  have eq23312 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20517 eq20404
    | exact resolve eq20404 eq20517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20404
  have eq23324 : (σ y) = (M.op (k (σ y) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23312 eq9347
    | exact resolve eq9347 eq23312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347 eq23312
  have eq23363 : (σ y) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20129 eq23324
    | exact resolve eq23324 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23324
  have eq23368 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20517 eq23363
    | exact resolve eq23363 eq20517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20517 eq23363
  have eq23370 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20181 eq23368
    | exact resolve eq23368 eq20181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23368
  have eq23371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20129 eq23370
    | exact resolve eq23370 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20129 eq23370
  have eq23372 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq23371
       have r₂ := eq27
       grind)
    | exact resolve eq23371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23371
  have eq23432 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23372 eq20156
    | exact resolve eq20156 eq23372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20156 eq23372
  have eq23440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20181 eq23432
    | exact resolve eq23432 eq20181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20181 eq23432
  have eq23475 : False := by grind
  exact eq23475

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq62 X2 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq62 X1 X0 X2
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op X0 X2) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq102 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq105 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq133 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq428 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq473 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq12
    | (have j1 := eq105 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq105 X0
       grind)
    | exact resolve eq12 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq491 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq492 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq491 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq491
    | (have j0 := eq491 X0
       grind)
    | exact resolve eq491 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq493 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq473
    | (have j0 := eq473 X0
       grind)
    | exact resolve eq473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq499 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq493 X0
       grind)
    | exact superpose eq493 eq12
    | (have j1 := eq493 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq493 X0
       grind)
    | exact resolve eq12 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq516 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq527 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq516 X0
       grind)
    | exact superpose eq516 eq10
    | (have j1 := eq516 X0
       grind)
    | exact resolve eq10 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq561 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq527 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq527
    | (have j0 := eq527 X0
       grind)
    | exact resolve eq527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq633 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131 x y
       grind)
    | exact superpose eq131 eq16
    | (have j1 := eq131 x y
       grind)
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq840 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq11
    | (have j1 := eq492 X0
       grind)
    | exact resolve eq11 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq842 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq840 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq840
    | (have j0 := eq840 X0
       grind)
    | exact resolve eq840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq889 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq842 X0
       grind)
    | exact superpose eq842 eq10
    | (have j1 := eq842 X0
       grind)
    | exact resolve eq10 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq918 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq889 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq889
    | (have j0 := eq889 (σ X0)
       grind)
    | exact resolve eq889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X0) = (M.op (M.op X1 (τ X0)) (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (τ X0) (τ X0)
       have i₂ := eq889 X0
       grind)
    | exact superpose eq889 eq62
    | (have j1 := eq889 X0
       grind)
    | exact resolve eq62 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq959 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq918 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq918
    | (have j0 := eq918 X0
       grind)
    | exact resolve eq918 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq918
  have eq967 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq959 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq959
    | (have j0 := eq959 X0
       grind)
    | exact resolve eq959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq969 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq967 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq967
    | (have j0 := eq967 X0
       grind)
    | exact resolve eq967 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq978 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq428 X0
       have i₂ := eq969 X0
       grind)
    | exact superpose eq969 eq428
    | (have j0 := eq428 X0
       have j1 := eq969 X0
       grind)
    | (have r₁ := eq428 X0
       have r₂ := eq969 X0
       grind)
    | exact resolve eq428 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq969
  have eq999 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq978 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1039 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X0) x
       have i₂ := eq999 X0
       grind)
    | exact superpose eq999 eq63
    | (have j1 := eq999 X0
       grind)
    | exact resolve eq63 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1042 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) X1 (σ X0)
       have i₂ := eq999 X0
       grind)
    | exact superpose eq999 eq68
    | (have j1 := eq999 X0
       grind)
    | exact resolve eq68 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq999
  have eq1523 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  clear eq934
  have eq1552 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq3003 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1552 (M.op X0 X0) (M.op x (τ X0))
       have i₂ := eq1552 X0 x
       grind)
    | exact superpose eq1552 eq1552
    | (have j0 := eq1552 (M.op X0 X0) x
       have j1 := eq1552 (M.op X0 X0) x
       grind)
    | exact resolve eq1552 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq3054 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3003 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq3003 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq3003
    | (have j0 := eq3003 X0
       grind)
    | exact resolve eq3003 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3064 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3054 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq3054 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq3054
    | (have j0 := eq3054 X0
       grind)
    | exact resolve eq3054 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3054
  have eq3065 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3064
  have eq3070 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3065 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3065
    | (have j0 := eq3065 (σ X0)
       grind)
    | exact resolve eq3065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065
  have eq3252 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1039
    | (have j0 := eq1039 (τ X0) X1
       grind)
    | exact resolve eq1039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq3296 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3252 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3252
    | (have j0 := eq3252 X0 X1
       grind)
    | exact resolve eq3252 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3321 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1042 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1042
    | (have j0 := eq1042 (τ X0) X1
       grind)
    | exact resolve eq1042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq3353 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3321 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3321
    | (have j0 := eq3321 X0 X1
       grind)
    | exact resolve eq3321 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3321
  have eq7831 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq7908 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7831 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7831
    | (have j0 := eq7831 X0 X1
       grind)
    | exact resolve eq7831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7831
  have eq16488 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3070 X0
       grind)
    | exact superpose eq3070 eq11
    | (have j1 := eq3070 X0
       grind)
    | exact resolve eq11 eq3070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq17900 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq16488 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16488
  have eq18212 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17900 (τ X0)
       have i₂ := eq3296 X0 X1
       grind)
    | exact superpose eq3296 eq17900
    | (have j1 := eq3296 X0 X1
       grind)
    | exact resolve eq17900 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq18213 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17900 (τ X0)
       have i₂ := eq3353 X0 X1
       grind)
    | exact superpose eq3353 eq17900
    | (have j1 := eq3353 X0 X1
       grind)
    | exact resolve eq17900 eq3353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353 eq17900
  have eq18269 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18213 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq18213
    | (have j0 := eq18213 X0 X1
       grind)
    | exact resolve eq18213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18213
  have eq18270 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18212 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq18212
    | (have j0 := eq18212 X0 X1
       grind)
    | exact resolve eq18212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18212
  have eq18284 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18269 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18269
    | (have j0 := eq18269 X0 X1
       grind)
    | exact resolve eq18269 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18269
  have eq18285 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (τ (k X0 X0))) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18270 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18270
    | (have j0 := eq18270 X0 X1
       grind)
    | exact resolve eq18270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18270
  have eq18292 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18284 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq18284
    | (have j0 := eq18284 X0 X1
       grind)
    | exact resolve eq18284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18284
  have eq18293 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 X0) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18285 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq18285
    | (have j0 := eq18285 X0 X1
       grind)
    | exact resolve eq18285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18285
  have eq18297 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18292 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18292
    | (have j0 := eq18292 X0 X1
       grind)
    | exact resolve eq18292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292
  have eq18298 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18293 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18293
    | (have j0 := eq18293 X0 X1
       grind)
    | exact resolve eq18293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18293
  have eq18301 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq18297 X0 X1
       have j1 := eq561 X0
       grind)
    | (have r₁ := eq18297 X0 X1
       have r₂ := eq561 X0
       grind)
    | exact resolve eq18297 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18297
  have eq18302 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq18298 X0 X1
       have j1 := eq561 X0
       grind)
    | (have r₁ := eq18298 X0 X1
       have r₂ := eq561 X0
       grind)
    | exact resolve eq18298 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq18298
  have eq18406 : ∀ X0 X2 : G, X0 ≠ X0 ∨ (k (M.op X0 X2) X0) = (M.op (M.op X0 X2) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq93 X0 (M.op x X0) X2
       have i₂ := eq18301 X0 x
       grind)
    | exact superpose eq18301 eq93
    | (have j1 := eq18301 X0 x
       grind)
    | (have r₁ := eq93 X0 (M.op x X0) X2
       have r₂ := eq18301 X0 x
       grind)
    | exact resolve eq93 eq18301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq18301
  have eq18426 : ∀ X0 X2 : G, (k (M.op X0 X2) X0) = (M.op (M.op X0 X2) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq18406 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18406
  have eq27232 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18426 X0 (M.op X0 x)
       have i₂ := eq18302 X0 x
       grind)
    | exact superpose eq18302 eq18426
    | (have j0 := eq18426 X0 x
       have j1 := eq18302 X0 x
       grind)
    | exact resolve eq18426 eq18302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18302 eq18426
  have eq27338 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq27232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27232
  have eq27535 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq27338 (σ X0)
       grind)
    | exact superpose eq27338 eq15
    | exact resolve eq15 eq27338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27571 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27535 X0
       have i₂ := eq27338 X0
       grind)
    | exact superpose eq27338 eq27535
    | exact resolve eq27535 eq27338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27338 eq27535
  have eq41658 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq633
       have i₂ := eq7908 x y
       grind)
    | exact superpose eq7908 eq633
    | (have j1 := eq7908 (σ x) (σ y)
       grind)
    | (have r₁ := eq633
       have r₂ := eq7908 x y
       grind)
    | (have r₁ := eq633
       have r₂ := eq7908 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq633
       have r₂ := eq7908 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq633 eq7908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41659 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq41658
  have eq467060 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41659
       grind)
    | exact superpose eq41659 eq16
    | exact resolve eq16 eq41659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41659
  have eq467061 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq467060
       have r₂ := eq27571 x
       grind)
    | exact resolve eq467060 eq27571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467060
  have eq467064 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq467061
       grind)
    | exact superpose eq467061 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq467061
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq467061
       grind)
    | exact resolve eq12 eq467061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467061
  have eq467116 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq467064
  have eq467716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq633
       have i₂ := eq467116
       grind)
    | exact superpose eq467116 eq633
    | exact resolve eq633 eq467116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq467116
  have eq467730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq467716
  have eq467731 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq467730
  have eq467774 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq467731
       grind)
    | exact superpose eq467731 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq467731
       grind)
    | exact resolve eq12 eq467731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467731
  have eq467826 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq467774
  have eq467853 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq467826
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq467826
    | exact resolve eq467826 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467826
  have eq479237 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq467853
       grind)
    | exact superpose eq467853 eq16
    | exact resolve eq16 eq467853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467853
  have eq479432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq479237
       have i₂ := eq7908 x y
       grind)
    | exact superpose eq7908 eq479237
    | (have j1 := eq7908 x y
       grind)
    | (have r₁ := eq479237
       have r₂ := eq7908 x y
       grind)
    | (have r₁ := eq479237
       have r₂ := eq7908 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq479237
       have r₂ := eq7908 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq479237 eq7908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7908
  have eq479433 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq479432
  have eq479437 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq479433
       grind)
    | exact superpose eq479433 eq16
    | exact resolve eq16 eq479433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479433
  have eq479458 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq479437
       have r₂ := eq27571 x
       grind)
    | exact resolve eq479437 eq27571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479437
  have eq479463 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq479458
       grind)
    | exact superpose eq479458 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq479458
       grind)
    | exact resolve eq12 eq479458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479458
  have eq479518 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq479463
  have eq479797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq479237
       have i₂ := eq479518
       grind)
    | exact superpose eq479518 eq479237
    | exact resolve eq479237 eq479518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479237 eq479518
  have eq479814 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq479797
  have eq479815 : (σ x) = (σ y) := by grind
  clear eq479814
  have eq479816 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq479815
       grind)
    | exact superpose eq479815 eq16
    | exact resolve eq16 eq479815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479822 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq479815
       grind)
    | exact superpose eq479815 eq10
    | exact resolve eq10 eq479815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479815
  have eq480127 : x = y := by
    first
    | (have i₁ := eq479822
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq479822
    | exact resolve eq479822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479822
  have eq480128 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq479816
       have i₂ := eq27571 x
       grind)
    | exact superpose eq27571 eq479816
    | exact resolve eq479816 eq27571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27571 eq479816
  have eq480204 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq480128
       have i₂ := eq480127
       grind)
    | exact superpose eq480127 eq480128
    | exact resolve eq480128 eq480127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480127 eq480128
  have eq480205 : False := by grind
  exact eq480205
