import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation854 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq61 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq73 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq127 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq9
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq9 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq445 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq445 X1 X0
       grind)
    | exact superpose eq445 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq445 X0 X1
       grind)
    | exact resolve eq13 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq522 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq1996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq148
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq148
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq148
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq148
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq148 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1997 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1996
  have eq2594 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 (M.op X0 (σ X1))
       have i₂ := eq522 X0 (σ X1)
       grind)
    | exact superpose eq522 eq41
    | (have j1 := eq522 X0 (σ X1)
       grind)
    | exact resolve eq41 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq522
  have eq4034 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0))))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq149 (τ X0) (τ X1) X2
       have i₂ := eq127 X1 X0
       grind)
    | exact superpose eq127 eq149
    | (have j0 := eq149 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq149 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq149
  have eq4108 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4034 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4034
    | (have j0 := eq4034 X0 X1 X2
       grind)
    | exact resolve eq4034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034
  have eq4111 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4108 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4108
    | (have j0 := eq4108 X0 X1 X2
       grind)
    | exact resolve eq4108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4113 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4111 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4111
    | (have j0 := eq4111 X0 X1 X2
       grind)
    | exact resolve eq4111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq4114 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4113 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4113
    | (have j0 := eq4113 X0 X1 X2
       grind)
    | exact resolve eq4113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4115 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4114 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4114
    | (have j0 := eq4114 X0 X1 X2
       grind)
    | exact resolve eq4114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq4116 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4115 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4115
    | (have j0 := eq4115 X0 X1 X2
       grind)
    | exact resolve eq4115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq55425 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (k X0 X1)
       have i₂ := eq4116 X0 X1 X0
       grind)
    | exact superpose eq4116 eq73
    | (have j1 := eq4116 X0 X1 x
       grind)
    | exact resolve eq73 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4116
  have eq119424 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2594 (σ x) y
       have i₂ := eq1997
       grind)
    | exact superpose eq1997 eq2594
    | exact resolve eq2594 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997 eq2594
  have eq119619 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq119424
  have eq119756 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq119619
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq119619
    | exact resolve eq119619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119619
  have eq119884 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq119756
       have r₂ := eq13 y x
       grind)
    | exact resolve eq119756 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119756
  have eq121161 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq159 x y
       have i₂ := eq119884
       grind)
    | exact superpose eq119884 eq159
    | (have j0 := eq159 x y
       grind)
    | exact resolve eq159 eq119884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq121171 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq55425 y x
       have i₂ := eq119884
       grind)
    | exact superpose eq119884 eq55425
    | (have j0 := eq55425 y x
       grind)
    | exact resolve eq55425 eq119884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55425 eq119884
  have eq121174 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq121171
  have eq121185 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq121161
  have eq121186 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq121185
  have eq125818 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq121186
       grind)
    | exact superpose eq121186 eq16
    | exact resolve eq16 eq121186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121186
  have eq126816 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq125818
       have i₂ := eq121174
       grind)
    | exact superpose eq121174 eq125818
    | exact resolve eq125818 eq121174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121174 eq125818
  have eq126817 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq126816
  have eq126818 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq126817
  have eq127559 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq126818
       grind)
    | exact superpose eq126818 eq10
    | exact resolve eq10 eq126818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126818
  have eq127776 : x = y ∨ x = y := by
    first
    | (have i₁ := eq127559
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq127559
    | exact resolve eq127559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127559
  have eq127777 : x = y := by grind
  clear eq127776
  have eq128531 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127777
       grind)
    | exact superpose eq127777 eq16
    | exact resolve eq16 eq127777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127777
  have eq128532 : False := by grind
  exact eq128532

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pyx_Equation856 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law856 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x x) (M.op x X0))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25 X0 (M.op X0 X0)
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq87 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq31
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq87 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq87
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq87 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq650 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq10
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq10 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq665 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq3069 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq3260 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3069 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3069
    | (have j0 := eq3069 X0 X1
       grind)
    | exact resolve eq3069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069
  have eq4025 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq665 x y
       grind)
    | exact superpose eq665 eq16
    | (have j1 := eq665 x y
       grind)
    | exact resolve eq16 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq8581 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq320 x y
       grind)
    | exact superpose eq320 eq16
    | (have j1 := eq320 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq320 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq320 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq13981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq4025
       have i₂ := eq3260 x y
       grind)
    | exact superpose eq3260 eq4025
    | (have j1 := eq3260 x y
       grind)
    | (have r₁ := eq4025
       have r₂ := eq3260 x y
       grind)
    | (have r₁ := eq4025
       have r₂ := eq3260 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4025
       have r₂ := eq3260 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4025 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260 eq4025
  have eq13985 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13981
  have eq13986 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13985
  have eq14252 : (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq14255 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq13986
       grind)
    | exact superpose eq13986 eq31
    | exact resolve eq31 eq13986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq14321 : y = (M.op y (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25 y y
       have i₂ := eq13986
       grind)
    | exact superpose eq13986 eq25
    | exact resolve eq25 eq13986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14365 : (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14252
  have eq14564 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8581
       have i₂ := eq14255
       grind)
    | exact superpose eq14255 eq8581
    | exact resolve eq8581 eq14255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8581
  have eq14567 : y = (M.op y (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq14255
       grind)
    | exact superpose eq14255 eq25
    | exact resolve eq25 eq14255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14255
  have eq14604 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14564
  have eq14605 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14604
  have eq16162 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14605
       have i₂ := eq14365
       grind)
    | exact superpose eq14365 eq14605
    | exact resolve eq14605 eq14365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14365 eq14605
  have eq16203 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16162
  have eq17497 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14567
       have i₂ := eq16203
       grind)
    | exact superpose eq16203 eq14567
    | exact resolve eq14567 eq16203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14567 eq16203
  have eq17544 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17497
  have eq17790 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14321
       have i₂ := eq17544
       grind)
    | exact superpose eq17544 eq14321
    | exact resolve eq14321 eq17544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321 eq17544
  have eq17832 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17790
  have eq17942 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13986
       have i₂ := eq17832
       grind)
    | exact superpose eq17832 eq13986
    | exact resolve eq13986 eq17832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13986 eq17832
  have eq18030 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq17942
  have eq18237 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18030
       grind)
    | exact superpose eq18030 eq10
    | exact resolve eq10 eq18030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18030
  have eq18309 : x = y ∨ x = y := by
    first
    | (have i₁ := eq18237
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18237
    | exact resolve eq18237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18237
  have eq18310 : x = y := by grind
  clear eq18309
  have eq18564 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18310
       grind)
    | exact superpose eq18310 eq16
    | exact resolve eq16 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310
  have eq18565 : False := by grind
  exact eq18565

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyx_pxy_Equation856 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law856 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x x) (M.op x X0))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25 X0 (M.op X0 X0)
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq53 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq81 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq31
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq81 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq424 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq10
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq10 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq424
    | (have j0 := eq424 X0 X1
       grind)
    | exact resolve eq424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq2107 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2107 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2107
    | (have j0 := eq2107 X0 X1
       grind)
    | exact resolve eq2107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107
  have eq2825 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq437 x y
       grind)
    | exact superpose eq437 eq16
    | (have j1 := eq437 x y
       grind)
    | exact resolve eq16 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq5950 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq307 x y
       grind)
    | exact superpose eq307 eq16
    | (have j1 := eq307 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq307 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq307 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq17100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2825
       have i₂ := eq2255 x y
       grind)
    | exact superpose eq2255 eq2825
    | (have j1 := eq2255 x y
       grind)
    | (have r₁ := eq2825
       have r₂ := eq2255 x y
       grind)
    | (have r₁ := eq2825
       have r₂ := eq2255 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2825
       have r₂ := eq2255 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2825 eq2255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255 eq2825
  have eq17105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17100
  have eq17106 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17105
  have eq17643 : (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq17646 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq17106
       grind)
    | exact superpose eq17106 eq31
    | exact resolve eq31 eq17106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq17707 : y = (M.op y (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25 y y
       have i₂ := eq17106
       grind)
    | exact superpose eq17106 eq25
    | exact resolve eq25 eq17106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17106
  have eq17755 : (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17643
  have eq18140 : (σ x) ≠ (σ x) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5950
       have i₂ := eq17646
       grind)
    | exact superpose eq17646 eq5950
    | exact resolve eq5950 eq17646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5950 eq17646
  have eq18187 : (σ x) ≠ (σ x) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18140
  have eq18188 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18187
  have eq19811 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18188
       have i₂ := eq17755
       grind)
    | exact superpose eq17755 eq18188
    | exact resolve eq18188 eq17755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17755 eq18188
  have eq19841 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19811
  have eq20592 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17707
       have i₂ := eq19841
       grind)
    | exact superpose eq19841 eq17707
    | exact resolve eq17707 eq19841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17707
  have eq20656 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20592
  have eq20893 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19841
       have i₂ := eq20656
       grind)
    | exact superpose eq20656 eq19841
    | exact resolve eq19841 eq20656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19841 eq20656
  have eq20959 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq20893
  have eq21266 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20959
       grind)
    | exact superpose eq20959 eq10
    | exact resolve eq10 eq20959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20959
  have eq21346 : x = y ∨ x = y := by
    first
    | (have i₁ := eq21266
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21266
    | exact resolve eq21266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21266
  have eq21347 : x = y := by grind
  clear eq21346
  have eq22067 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21347
       grind)
    | exact superpose eq21347 eq16
    | exact resolve eq16 eq21347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21347
  have eq22068 : False := by grind
  exact eq22068

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation860 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq48 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq215 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49 x y
       grind)
    | exact superpose eq49 eq16
    | (have j1 := eq49 x y
       grind)
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1167 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1206 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1167
    | (have j0 := eq1167 X0 X1
       grind)
    | exact resolve eq1167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1624 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq215
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq215
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq215
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq215
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq215 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1625 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1624
  have eq31829 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1625
       grind)
    | exact superpose eq1625 eq16
    | exact resolve eq16 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31854 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1625
       grind)
    | exact superpose eq1625 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1625
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1625
       grind)
    | exact resolve eq13 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq31968 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq31854
  have eq31969 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq31968
  have eq31971 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq31969
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq31969
    | exact resolve eq31969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31969
  have eq32867 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1206 y x
       have i₂ := eq31971
       grind)
    | exact superpose eq31971 eq1206
    | (have j0 := eq1206 y x
       grind)
    | exact resolve eq1206 eq31971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq32868 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq31971
       grind)
    | exact superpose eq31971 eq10
    | exact resolve eq10 eq31971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31971
  have eq32932 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32867
  have eq32967 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq32868
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32868
    | exact resolve eq32868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32868
  have eq32968 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq32932
       have r₂ := eq31829
       grind)
    | exact resolve eq32932 eq31829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829 eq32932
  have eq32971 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq32967
       have r₂ := eq13 x y
       grind)
    | exact resolve eq32967 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32967
  have eq34340 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq227 x y
       have i₂ := eq32971
       grind)
    | exact superpose eq32971 eq227
    | (have j0 := eq227 x y
       grind)
    | exact resolve eq227 eq32971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq32971
  have eq34354 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34340
  have eq34355 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34354
  have eq34747 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq34355
       grind)
    | exact superpose eq34355 eq16
    | exact resolve eq16 eq34355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34355
  have eq35416 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34747
       have i₂ := eq32968
       grind)
    | exact superpose eq32968 eq34747
    | exact resolve eq34747 eq32968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32968 eq34747
  have eq35417 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35416
  have eq35418 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq35417
  have eq35869 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35418
       grind)
    | exact superpose eq35418 eq10
    | exact resolve eq10 eq35418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35418
  have eq35956 : x = y ∨ x = y := by
    first
    | (have i₁ := eq35869
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35869
    | exact resolve eq35869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35869
  have eq35957 : x = y := by grind
  clear eq35956
  have eq36806 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35957
       grind)
    | exact superpose eq35957 eq16
    | exact resolve eq16 eq35957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35957
  have eq36807 : False := by grind
  exact eq36807

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation947 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq65 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X2 X2 X1
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
       have i₂ := eq26 X1 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq264 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq261 X1 x X2 X3
       have i₂ := eq195 x X1 (M.op X2 x)
       grind)
    | exact superpose eq195 eq261
    | exact resolve eq261 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq282 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X1 X3
    first
    | (have i₁ := eq264 x X1 X3
       have i₂ := eq195 x X1 x
       grind)
    | exact superpose eq195 eq264
    | exact resolve eq264 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq350 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq195 X1 x X0
       grind)
    | exact superpose eq195 eq9
    | exact resolve eq9 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq519 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq350 X2 (M.op X0 X1)
       have i₂ := eq195 X1 X0 X0
       grind)
    | exact superpose eq195 eq350
    | exact resolve eq350 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq350
    | exact resolve eq350 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq350 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq350 (M.op X0 X0) X0
       grind)
    | exact superpose eq350 eq350
    | exact resolve eq350 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X1 X0 X0
       have i₂ := eq350 X1 (M.op X0 X1)
       grind)
    | exact superpose eq350 eq25
    | exact resolve eq25 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq552 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq195 X1 X0 X0
       grind)
    | exact superpose eq195 eq528
    | exact resolve eq528 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq600 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1 (M.op X0 X0)
       have i₂ := eq523 X0
       grind)
    | exact superpose eq523 eq195
    | exact resolve eq195 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq552 (M.op X1 X0) X0
       grind)
    | exact superpose eq552 eq600
    | exact resolve eq600 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq614 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq552 (M.op X0 X0) X0
       grind)
    | exact superpose eq552 eq609
    | exact resolve eq609 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq618 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq523 X0
       grind)
    | exact superpose eq523 eq614
    | exact resolve eq614 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq614
  have eq641 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq66
    | exact resolve eq66 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq673 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq641 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq641
    | exact resolve eq641 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq690 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq673 X0
       have i₂ := eq552 (M.op X0 X0) X0
       grind)
    | exact superpose eq552 eq673
    | exact resolve eq673 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq700 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq690 X0
       have i₂ := eq618 X0 X0
       grind)
    | exact superpose eq618 eq690
    | exact resolve eq690 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1771 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq282 (M.op X1 X1) x
       have i₂ := eq350 (M.op X1 X1) X1
       grind)
    | exact superpose eq350 eq282
    | exact resolve eq282 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq350
  have eq1834 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1771 (M.op X1 (σ (M.op X0 X0))) X1
       have i₂ := eq520 X0 X1
       grind)
    | exact superpose eq520 eq1771
    | exact resolve eq1771 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq1771
  have eq1911 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1834 X0 X1
       have i₂ := eq195 (σ (M.op X0 X0)) X1 X1
       grind)
    | exact superpose eq195 eq1834
    | exact resolve eq1834 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq1834
  have eq1932 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1911 X0 X1
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq1911
    | exact resolve eq1911 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1943 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) = (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1932 X0 X1
       have i₂ := eq552 (M.op X0 X0) X0
       grind)
    | exact superpose eq552 eq1932
    | exact resolve eq1932 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq1932
  have eq1951 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1943 X0 X1
       have i₂ := eq618 X0 X0
       grind)
    | exact superpose eq618 eq1943
    | exact resolve eq1943 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq1943
  have eq3382 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq519 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq519
    | exact resolve eq519 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3791 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq700 X1
       have i₂ := eq3382 X1 X1 X0
       grind)
    | (have i₁ := eq700 X1
       have i₂ := eq3382 X1 X0 X1
       grind)
    | exact superpose eq3382 eq700
    | exact resolve eq700 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq3800 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq519 X1 X1 X2
       have i₂ := eq3382 X1 X1 X0
       grind)
    | (have i₁ := eq519 X1 X1 X2
       have i₂ := eq3382 X1 X0 X1
       grind)
    | exact superpose eq3382 eq519
    | exact resolve eq519 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq3382
  have eq5124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq433
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq433
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq433
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq433
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq433 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq5126 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq5124
  have eq5695 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op (σ (M.op X1 (M.op X1 X0))) (M.op (σ X0) (σ (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X1 (M.op X1 X0)) (σ X0)
       have i₂ := eq3791 X1 X0
       grind)
    | exact superpose eq3791 eq65
    | exact resolve eq65 eq3791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq3791
  have eq5739 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5695 X0 X1
       have i₂ := eq1951 (M.op X1 (M.op X1 X0)) (σ X0)
       grind)
    | exact superpose eq1951 eq5695
    | exact resolve eq5695 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq5695
  have eq5793 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5739 X0 X1
       have i₂ := eq3800 X1 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq3800 eq5739
    | exact resolve eq5739 eq3800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800 eq5739
  have eq165344 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5126
       grind)
    | exact superpose eq5126 eq10
    | exact resolve eq10 eq5126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126
  have eq165345 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq165344
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq165344
    | exact resolve eq165344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165344
  have eq165346 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq165345
  have eq165479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5793 x x
       have i₂ := eq165346
       grind)
    | exact superpose eq165346 eq5793
    | exact resolve eq5793 eq165346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793 eq165346
  have eq165562 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq165479
       have r₂ := eq16
       grind)
    | exact resolve eq165479 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165479
  have eq165588 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq165562
       grind)
    | exact superpose eq165562 eq10
    | exact resolve eq10 eq165562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165562
  have eq165686 : x = y ∨ x = y := by
    first
    | (have i₁ := eq165588
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq165588
    | exact resolve eq165588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165588
  have eq165687 : x = y := by grind
  clear eq165686
  have eq165703 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq165687
       grind)
    | exact superpose eq165687 eq16
    | exact resolve eq16 eq165687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165687
  have eq165704 : False := by grind
  exact eq165704

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq72 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq72
    | exact resolve eq72 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq80
    | exact resolve eq80 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq80
  have eq415 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq59 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq10
    | (have j1 := eq59 X1 X0
       grind)
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq427 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq415
    | (have j0 := eq415 X0 X1
       grind)
    | exact resolve eq415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq1042 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq81 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8129 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq427 y x
       grind)
    | exact superpose eq427 eq16
    | (have j1 := eq427 y x
       grind)
    | exact resolve eq16 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq165951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1042 y x
       grind)
    | exact superpose eq1042 eq16
    | (have j1 := eq1042 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1042 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1042 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1042 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq165952 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq165951
  have eq165953 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8129
       have i₂ := eq165952
       grind)
    | exact superpose eq165952 eq8129
    | exact resolve eq8129 eq165952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8129 eq165952
  have eq165954 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq165953
  have eq165992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81 x
       have i₂ := eq165954
       grind)
    | exact superpose eq165954 eq81
    | exact resolve eq81 eq165954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq165954
  have eq166361 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq165992
       have r₂ := eq16
       grind)
    | exact resolve eq165992 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165992
  have eq166397 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq166361
       grind)
    | exact superpose eq166361 eq10
    | exact resolve eq10 eq166361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166361
  have eq166478 : x = y ∨ x = y := by
    first
    | (have i₁ := eq166397
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq166397
    | exact resolve eq166397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166397
  have eq166479 : x = y := by grind
  clear eq166478
  have eq166500 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166479
       grind)
    | exact superpose eq166479 eq16
    | exact resolve eq16 eq166479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166479
  have eq166501 : False := by grind
  exact eq166501

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq55 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq55
    | exact resolve eq55 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq60
    | exact resolve eq60 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq62 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq57
    | exact resolve eq57 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq81 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X1 X1) X1 X2 X1
       have i₂ := eq25 X1 X1
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq93
    | exact resolve eq93 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq82 X0 X1 X2 X3 X4
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq82
    | exact resolve eq82 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq103 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 (M.op X0 X1) x
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq89
    | exact resolve eq89 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq91 X0 X0 X0
       grind)
    | exact superpose eq91 eq9
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (M.op x (M.op x x)) x
       have i₂ := eq91 x x x
       grind)
    | exact superpose eq91 eq89
    | exact resolve eq89 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq513 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq68 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq68
    | exact resolve eq68 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq68
  have eq535 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq513 X0
       have i₂ := eq25 (τ X0) (τ X0)
       grind)
    | exact superpose eq25 eq513
    | exact resolve eq513 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq513
  have eq542 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq535 X0
       have i₂ := eq406 (τ X0) (τ X0)
       grind)
    | exact superpose eq406 eq535
    | exact resolve eq535 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq535
  have eq545 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq542 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542
    | exact resolve eq542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq575 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq545 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq545
    | exact resolve eq545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq865 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq59 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1126 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2
       have i₂ := eq397 X2 X0 X1
       grind)
    | exact superpose eq397 eq57
    | exact resolve eq57 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1576 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1126 (M.op X0 (M.op X0 X0)) (M.op (M.op x x) (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq84 X0 x x
       grind)
    | exact superpose eq84 eq1126
    | exact resolve eq1126 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq2397 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq94 (M.op (M.op x x) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0))) x x
       have i₂ := eq81 X0 X1 x x X4
       grind)
    | exact superpose eq81 eq94
    | exact resolve eq94 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2429 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94 (M.op X1 (M.op X2 X3)) X0 X3 X2
       have i₂ := eq397 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq397 eq94
    | exact resolve eq94 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq397
  have eq2528 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2429 X0 X1 X2 X3
       have i₂ := eq865 X0 (M.op X1 (M.op X2 X3)) X0
       grind)
    | exact superpose eq865 eq2429
    | exact resolve eq2429 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2557 : ∀ X0 X1 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq2397 X0 X1 X4 X5 X6
       have i₂ := eq865 (M.op X4 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq865 eq2397
    | exact resolve eq2397 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2630 : ∀ X0 X1 X5 X6 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq2557 X0 X1 x X5 X6
       have i₂ := eq175 X1 X0 x
       grind)
    | exact superpose eq175 eq2557
    | exact resolve eq2557 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2557
  have eq4419 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (τ X0) (τ X1)
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq143
    | (have j0 := eq143 (τ X0) (τ X1)
       grind)
    | exact resolve eq143 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq143
  have eq4427 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4419 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4419
    | (have j0 := eq4419 X0 X1
       grind)
    | exact resolve eq4419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq4431 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4427 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4427
    | (have j0 := eq4427 X0 X1
       grind)
    | exact resolve eq4427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq4433 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4431 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4431
    | (have j0 := eq4431 X0 X1
       grind)
    | exact resolve eq4431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4431
  have eq4434 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4433 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4433
    | (have j0 := eq4433 X0 X1
       grind)
    | exact resolve eq4433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4433
  have eq4435 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4434 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4434
    | (have j0 := eq4434 X0 X1
       grind)
    | exact resolve eq4434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434
  have eq4436 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4435 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4435
    | (have j0 := eq4435 X0 X1
       grind)
    | exact resolve eq4435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq4803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq138
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq138
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq138 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq4804 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4803
  have eq5124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X1 (M.op X1 X1)) (M.op X1 X0) X2 X3 X0
       have i₂ := eq1576 X1 X0
       grind)
    | exact superpose eq1576 eq99
    | exact resolve eq99 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1576
  have eq5407 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5124 X0 X1 X2 X3
       have i₂ := eq865 (M.op X1 X0) (M.op X1 (M.op X1 X1)) (M.op X1 X0)
       grind)
    | exact superpose eq865 eq5124
    | exact resolve eq5124 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5124
  have eq5538 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5407 X0 X1 X2 X3
       have i₂ := eq2528 (M.op X1 X0) X1 X1 X1
       grind)
    | exact superpose eq2528 eq5407
    | exact resolve eq5407 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528 eq5407
  have eq5612 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X0) = (M.op X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5538 X0 X1 X2 X3
       have i₂ := eq865 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq865 eq5538
    | exact resolve eq5538 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq5538
  have eq5653 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5612 X0 X1 X2 X3
       have i₂ := eq2630 X1 X0 X0 X1
       grind)
    | exact superpose eq2630 eq5612
    | exact resolve eq5612 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612
  have eq5663 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5653 X0 X1 x x
       have i₂ := eq89 X0 (M.op x x)
       grind)
    | exact superpose eq89 eq5653
    | exact resolve eq5653 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq5653
  have eq45570 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5663 X3 X2
       have i₂ := eq2630 X2 X3 X0 X1
       grind)
    | exact superpose eq2630 eq5663
    | exact resolve eq5663 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq5663
  have eq169494 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4804
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4804
       grind)
    | exact resolve eq13 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq169678 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq169494
  have eq169679 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq169678
  have eq169757 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq169679
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq169679
    | exact resolve eq169679 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169679
  have eq843312 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq169757
       grind)
    | exact superpose eq169757 eq10
    | exact resolve eq10 eq169757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169757
  have eq843313 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq843312
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq843312
    | exact resolve eq843312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843312
  have eq843314 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq843313
       have r₂ := eq13 x y
       grind)
    | exact resolve eq843313 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843313
  have eq843317 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4436 x y
       have i₂ := eq843314
       grind)
    | exact superpose eq843314 eq4436
    | (have j0 := eq4436 x y
       grind)
    | (have r₁ := eq4436 x y
       have r₂ := eq843314
       grind)
    | exact resolve eq4436 eq843314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436 eq843314
  have eq843318 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq843317
  have eq843319 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq843318
  have eq844440 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq45570 X0 X1 x y
       have i₂ := eq843319
       grind)
    | exact superpose eq843319 eq45570
    | exact resolve eq45570 eq843319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45570
  have eq844462 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq844440 x x
       have i₂ := eq1126 x x x
       grind)
    | exact superpose eq1126 eq844440
    | exact resolve eq844440 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq844440
  have eq844585 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq575 y
       have i₂ := eq844462
       grind)
    | exact superpose eq844462 eq575
    | exact resolve eq575 eq844462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq844462
  have eq855919 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq844585
       grind)
    | exact superpose eq844585 eq16
    | exact resolve eq16 eq844585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844585
  have eq856179 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq855919
       have i₂ := eq843319
       grind)
    | exact superpose eq843319 eq855919
    | exact resolve eq855919 eq843319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843319 eq855919
  have eq856180 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq856179
  have eq856181 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq856180
  have eq857039 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq856181
       grind)
    | exact superpose eq856181 eq10
    | exact resolve eq10 eq856181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856181
  have eq857370 : x = y ∨ x = y := by
    first
    | (have i₁ := eq857039
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq857039
    | exact resolve eq857039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857039
  have eq857371 : x = y := by grind
  clear eq857370
  have eq857402 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq857371
       grind)
    | exact superpose eq857371 eq16
    | exact resolve eq16 eq857371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857371
  have eq857403 : False := by grind
  exact eq857403
