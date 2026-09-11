import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq47 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq48 (τ X0)
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq55 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq50
    | exact resolve eq50 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq60 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq55
    | exact resolve eq55 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq55
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq57 X1
       grind)
    | exact superpose eq57 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq98 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq173 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | (have j0 := eq89 X1 X1
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq192 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq173
    | (have j0 := eq173 X0 X1
       grind)
    | exact resolve eq173 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq173
  have eq198 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq192 X0 X0
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq192 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq192
  have eq202 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq198
  have eq458 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202
    | exact resolve eq202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq512 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq458 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq458 X0 X1
       grind)
    | exact superpose eq458 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq458 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq458 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq458 X0 X1
       grind)
    | exact resolve eq13 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq529 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq525 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq525 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq525 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq578 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq529 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq582 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq578 X0 X1
       have j1 := eq458 X1 X0
       grind)
    | (have r₁ := eq578 X0 X0
       have r₂ := eq458 X0 X0
       grind)
    | (have r₁ := eq578 X1 X0
       have r₂ := eq458 X0 X1
       grind)
    | exact resolve eq578 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq578
  have eq691 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq582 (σ X1) (σ X0)
       grind)
    | exact superpose eq582 eq15
    | exact resolve eq15 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq582 X1 X0
       grind)
    | exact superpose eq582 eq691
    | exact resolve eq691 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq691
  have eq1164 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq710 x y
       grind)
    | exact superpose eq710 eq16
    | (have r₁ := eq16
       have r₂ := eq710 x y
       grind)
    | exact resolve eq16 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1183 : False := by grind
  exact eq1183

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_x_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) = (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq92 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq95 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq289 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq297 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq289 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq289
    | (have j0 := eq289 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq289 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq289
  have eq302 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq529 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq569 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq529
    | (have j0 := eq529 X1 X1
       grind)
    | exact resolve eq529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq4296 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4319 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4296 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4296
    | (have r₁ := eq4296 X0 (τ X0)
       have r₂ := eq11 X0
       grind)
    | (have r₁ := eq4296 (σ (τ (σ X1))) X1
       have r₂ := eq11 (σ X1)
       grind)
    | exact resolve eq4296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4340 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4319 X0 X1
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq4319
    | (have j0 := eq4319 X0 X1
       grind)
    | (have r₁ := eq4319 (k (τ X1) (τ X0)) (τ (k X1 X0))
       have r₂ := eq37 X0 X1
       grind)
    | (have r₁ := eq4319 (τ (k X1 X0)) (k (τ X1) (τ X0))
       have r₂ := eq37 X0 X1
       grind)
    | exact resolve eq4319 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq4546 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4340 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4575 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq4546 (σ X0)
       grind)
    | exact superpose eq4546 eq41
    | (have j1 := eq4546 (σ X0)
       grind)
    | exact resolve eq41 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4546
  have eq4580 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4575 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4575
    | (have j0 := eq4575 X0
       grind)
    | exact resolve eq4575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4575
  have eq4595 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4580 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq4580
    | (have j0 := eq4580 X0
       grind)
    | exact resolve eq4580 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4580
  have eq4600 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4595 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4595
    | (have j0 := eq4595 X0
       grind)
    | exact resolve eq4595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4595
  have eq4601 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4600 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq4708 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4601 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4601
    | exact resolve eq4601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4734 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4601 X0
       grind)
    | exact superpose eq4601 eq11
    | exact resolve eq11 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4798 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4708 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq4708
    | exact resolve eq4708 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4708
  have eq4827 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4798 X0
       grind)
    | exact superpose eq4798 eq11
    | exact resolve eq11 eq4798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4798
  have eq4936 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4827 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4827
    | exact resolve eq4827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq5529 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5530 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq4734 X0
       grind)
    | exact superpose eq4734 eq9
    | exact resolve eq9 eq4734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5555 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5530 X0 X1
       have i₂ := eq4936 X0
       grind)
    | exact superpose eq4936 eq5530
    | exact resolve eq5530 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq5556 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5529 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5529
    | exact resolve eq5529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529
  have eq5597 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5556 X0
       have i₂ := eq4936 X0
       grind)
    | exact superpose eq4936 eq5556
    | exact resolve eq5556 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556
  have eq5614 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5597
  have eq7199 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4601 X0
       have i₂ := eq92 X1 X0
       grind)
    | exact superpose eq92 eq4601
    | (have j1 := eq92 X1 X0
       grind)
    | exact resolve eq4601 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq4601
  have eq7237 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7199 X0 X1
       have i₂ := eq4936 X0
       grind)
    | exact superpose eq4936 eq7199
    | (have j0 := eq7199 X0 X1
       grind)
    | exact resolve eq7199 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq7265 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7237 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7237
    | (have j0 := eq7237 X0 X1
       grind)
    | exact resolve eq7237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7237
  have eq7287 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7265 X0 X1
       have i₂ := eq4734 X0
       grind)
    | exact superpose eq4734 eq7265
    | (have j0 := eq7265 X0 X1
       grind)
    | exact resolve eq7265 eq4734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4734 eq7265
  have eq7306 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7287 X0 X1
       have i₂ := eq4936 X0
       grind)
    | exact superpose eq4936 eq7287
    | (have j0 := eq7287 X0 X1
       grind)
    | exact resolve eq7287 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936 eq7287
  have eq7358 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5555 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq5555
    | exact resolve eq5555 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555
  have eq7456 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7358 X0 X1 X2
       have i₂ := eq302 X0 X1
       grind)
    | exact superpose eq302 eq7358
    | exact resolve eq7358 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7358
  have eq7496 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7456 X0 X1 X2
       have i₂ := eq302 X0 X1
       grind)
    | exact superpose eq302 eq7456
    | exact resolve eq7456 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq7456
  have eq322545 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq7306 X1 X0
       grind)
    | exact superpose eq7306 eq11
    | (have j1 := eq7306 X1 X0
       grind)
    | exact resolve eq11 eq7306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7306
  have eq322733 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq322545 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq322545
    | (have j0 := eq322545 X0 X1
       grind)
    | exact resolve eq322545 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq322545
  have eq324052 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq322733 (σ X0) X1
       grind)
    | exact superpose eq322733 eq15
    | (have j1 := eq322733 (σ X0) X1
       grind)
    | exact resolve eq15 eq322733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322733
  have eq763800 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq324052 x y
       grind)
    | exact superpose eq324052 eq16
    | (have j1 := eq324052 x y
       grind)
    | exact resolve eq16 eq324052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324052
  have eq765580 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq763800
       have i₂ := eq569 x y
       grind)
    | exact superpose eq569 eq763800
    | (have j1 := eq569 y y
       grind)
    | (have r₁ := eq763800
       have r₂ := eq569 x y
       grind)
    | exact resolve eq763800 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq763800
  have eq765581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq765580
  have eq765582 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq765581
  have eq767618 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq765582
       grind)
    | exact superpose eq765582 eq10
    | exact resolve eq10 eq765582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765582
  have eq767955 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq767618
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq767618
    | exact resolve eq767618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767618
  have eq767956 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq767955
  have eq768197 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq767956
       grind)
    | exact superpose eq767956 eq9
    | exact resolve eq9 eq767956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767956
  have eq777388 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5614 y
       have i₂ := eq768197 X0
       grind)
    | exact superpose eq768197 eq5614
    | (have j1 := eq768197 X0
       grind)
    | exact resolve eq5614 eq768197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5614 eq768197
  have eq777692 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have j0 := eq777388 X0
       grind)
    | (have r₁ := eq777388 X0
       have r₂ := eq16
       grind)
    | exact resolve eq777388 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777388
  have eq781802 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq777692 y
       grind)
    | exact superpose eq777692 eq9
    | exact resolve eq9 eq777692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781848 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq7496 y y X0
       have i₂ := eq777692 y
       grind)
    | exact superpose eq777692 eq7496
    | exact resolve eq7496 eq777692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7496 eq777692
  have eq786528 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq781848 (σ x)
       grind)
    | exact superpose eq781848 eq16
    | exact resolve eq16 eq781848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781848
  have eq786810 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq786528
       have i₂ := eq781802 x
       grind)
    | exact superpose eq781802 eq786528
    | exact resolve eq786528 eq781802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781802 eq786528
  have eq786811 : False := by grind
  exact eq786811

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq9 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq69 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq71 (τ X0) X1 X2
       grind)
    | exact superpose eq71 eq17
    | exact resolve eq17 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq92 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq99 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq72 (σ X0) X1 X2
       grind)
    | exact superpose eq72 eq30
    | exact resolve eq30 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq105 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq144 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))
       have i₂ := eq92 (τ X0) X1 X2
       grind)
    | exact superpose eq92 eq17
    | exact resolve eq17 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq147 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144
    | exact resolve eq144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq166 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq76
    | (have j0 := eq76 X2 X2
       grind)
    | exact resolve eq76 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq184 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq186 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq201 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))
       have i₂ := eq147 (τ X0) X1 X2
       grind)
    | exact superpose eq147 eq17
    | exact resolve eq17 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201
    | exact resolve eq201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq439 : ∀ X0 X1 X2 : G, (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1)))))) ≠ (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1)))))) ∨ (k X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X2
       have i₂ := eq105 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X0 X1
       grind)
    | exact superpose eq105 eq186
    | (have j0 := eq186 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X2
       grind)
    | exact resolve eq186 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq186
  have eq446 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq439 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq458 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq446 X0 X1 X2
       have i₂ := eq11 (τ (M.op X0 (M.op X1 (M.op X0 X1))))
       grind)
    | exact superpose eq11 eq446
    | exact resolve eq446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq469 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq458 X0 X1 X2
       have i₂ := eq72 X2 X0 X1
       grind)
    | exact superpose eq72 eq458
    | exact resolve eq458 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq458
  have eq2230 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X3)) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) X3
       have i₂ := eq147 (τ X0) X1 X2
       grind)
    | exact superpose eq147 eq166
    | (have j0 := eq166 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) X3
       grind)
    | exact resolve eq166 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq166
  have eq2298 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (σ X3) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2230 X0 X1 X2 X3
       have i₂ := eq204 X0 X1 X2
       grind)
    | exact superpose eq204 eq2230
    | (have j0 := eq2230 X0 X1 X2 X3
       grind)
    | exact resolve eq2230 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2321 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ X3) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2298 X0 X1 X2 X3
       have i₂ := eq17 X0 X3
       grind)
    | exact superpose eq17 eq2298
    | (have j0 := eq2298 X0 X1 X2 X3
       grind)
    | exact resolve eq2298 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq2339 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ X3) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq2321 X0 X1 X2 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq2321 X0 X1 X2 X3
       have r₂ := eq12 X0 (σ X3)
       grind)
    | exact resolve eq2321 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2354 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ X3) = (M.op X0 (σ X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq2339 X0 x x X3
       have i₂ := eq204 X0 x x
       grind)
    | exact superpose eq204 eq2339
    | (have j0 := eq2339 X0 x x X3
       grind)
    | exact resolve eq2339 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq2339
  have eq3220 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2354 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2354
    | exact resolve eq2354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2354 (σ X0) X1
       grind)
    | exact superpose eq2354 eq15
    | (have j1 := eq2354 (σ X0) X1
       grind)
    | exact resolve eq15 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq3344 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq3220 X1 (τ X0)
       grind)
    | exact superpose eq3220 eq17
    | (have j1 := eq3220 X1 (τ X0)
       grind)
    | exact resolve eq17 eq3220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3220
  have eq4995 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3344 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3344
    | exact resolve eq3344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq5101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4995 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4995
    | (have j0 := eq4995 X0 X1
       grind)
    | exact resolve eq4995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995
  have eq19512 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3256 x y
       grind)
    | exact superpose eq3256 eq16
    | (have j1 := eq3256 x y
       grind)
    | exact resolve eq16 eq3256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19627 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3256 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq20712 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19512
       have i₂ := eq5101 x y
       grind)
    | exact superpose eq5101 eq19512
    | (have j1 := eq5101 (σ x) (σ y)
       grind)
    | (have r₁ := eq19512
       have r₂ := eq5101 x y
       grind)
    | exact resolve eq19512 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20715 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20712
  have eq20719 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20715
       grind)
    | exact superpose eq20715 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20715
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20715
       grind)
    | exact resolve eq13 eq20715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20715
  have eq20792 : y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20719
  have eq35137 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19627 x y
       have i₂ := eq20792
       grind)
    | exact superpose eq20792 eq19627
    | (have j0 := eq19627 x y
       grind)
    | exact resolve eq19627 eq20792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19627 eq20792
  have eq35144 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq35137
  have eq35145 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35144
  have eq35165 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq35145
       grind)
    | exact superpose eq35145 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq35145
       grind)
    | exact resolve eq12 eq35145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35145
  have eq35257 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq35165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35165
  have eq35488 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19512
       have i₂ := eq35257 x
       grind)
    | exact superpose eq35257 eq19512
    | exact resolve eq19512 eq35257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19512 eq35257
  have eq35492 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35488
  have eq35493 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35492
  have eq35498 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35493
       grind)
    | exact superpose eq35493 eq16
    | exact resolve eq16 eq35493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35499 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq35493
       grind)
    | exact superpose eq35493 eq9
    | exact resolve eq9 eq35493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35500 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq35493
       grind)
    | exact superpose eq35493 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq35493
       grind)
    | exact resolve eq13 eq35493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35531 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (M.op (σ y) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq469 (σ x) (σ y) X0
       have i₂ := eq35493
       grind)
    | exact superpose eq35493 eq469
    | exact resolve eq469 eq35493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq35591 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq35500
  have eq35592 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq35591
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq35591
    | exact resolve eq35591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35591
  have eq43364 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5101 x y
       have i₂ := eq35592
       grind)
    | exact superpose eq35592 eq5101
    | (have j0 := eq5101 x y
       grind)
    | exact resolve eq5101 eq35592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101 eq35592
  have eq43454 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq43364
       have r₂ := eq35498
       grind)
    | exact resolve eq43364 eq35498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43364
  have eq43944 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq35498
       have i₂ := eq43454
       grind)
    | exact superpose eq43454 eq35498
    | exact resolve eq35498 eq43454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35498 eq43454
  have eq44040 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq43944
  have eq44046 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35499 X0
       have i₂ := eq44040
       grind)
    | exact superpose eq44040 eq35499
    | exact resolve eq35499 eq44040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35499
  have eq44058 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35531 X0
       have i₂ := eq44040
       grind)
    | exact superpose eq44040 eq35531
    | exact resolve eq35531 eq44040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35531 eq44040
  have eq44250 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq44058 X0
       have i₂ := eq35493
       grind)
    | exact superpose eq35493 eq44058
    | exact resolve eq44058 eq35493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44058
  have eq44262 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq44046 X0
       have i₂ := eq35493
       grind)
    | exact superpose eq35493 eq44046
    | exact resolve eq44046 eq35493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35493 eq44046
  have eq44359 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq44250 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq44250
    | exact resolve eq44250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44250
  have eq46389 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44262 (σ x)
       grind)
    | exact superpose eq44262 eq16
    | exact resolve eq16 eq44262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44262
  have eq46506 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq46389
       have i₂ := eq44359 x
       grind)
    | exact superpose eq44359 eq46389
    | exact resolve eq46389 eq44359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44359 eq46389
  have eq46507 : False := by grind
  exact eq46507

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
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
  clear eq24
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
  have eq53 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X0 (M.op X3 X4)) X5) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X4)) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op X3 X4)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq76
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq76 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq373 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq555 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq373
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq373 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X0 (M.op x y)) X5) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq53 X0 X1 X2 x x X5
       have i₂ := eq373 X0 x x
       grind)
    | (have i₁ := eq53 X0 X1 X2 x y X5
       have i₂ := eq373 X0 X1 X2
       grind)
    | exact superpose eq373 eq53
    | (have j0 := eq53 X0 X1 X2 x y X5
       grind)
    | exact resolve eq53 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq606 : ∀ X0 X5 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op X0 (M.op x y)) X5) X5) := by
    intro X0 X5
    first
    | (have i₁ := eq605 X0 x x X5
       have i₂ := eq373 X0 x x
       grind)
    | (have i₁ := eq605 X0 x y X5
       have i₂ := eq373 X0 x x
       grind)
    | exact superpose eq373 eq605
    | (have j0 := eq605 X0 x y X5
       grind)
    | exact resolve eq605 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq673 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq606 eq14
    | exact resolve eq14 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq695 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq673 X0 x x
       have i₂ := eq373 (M.op X0 sF0) x x
       grind)
    | (have i₁ := eq673 X0 x y
       have i₂ := eq373 (M.op X0 sF0) x x
       grind)
    | exact superpose eq373 eq673
    | (have j0 := eq673 X0 x y
       grind)
    | exact resolve eq673 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq1149 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op x y)) ∨ (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq69 X0 X1 x X3
       have i₂ := eq555 (M.op X0 X1) x
       grind)
    | exact superpose eq555 eq69
    | (have j0 := eq69 X0 X1 x X3
       grind)
    | exact resolve eq69 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq113 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1404
    | exact resolve eq1404 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1408 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1405
       have r₂ := eq27
       grind)
    | exact resolve eq1405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1418 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1408 eq373
    | exact resolve eq373 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1514 : (σ x) = (M.op (σ y) (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1418 eq1408
    | exact resolve eq1408 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq1418
  have eq1515 : (σ x) = (M.op (σ y) (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq1514
  have eq1550 : (σ x) = (M.op (σ x) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1515 eq695
    | exact resolve eq695 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq1515
  have eq1594 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (M.op x y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1550 eq1149
    | exact resolve eq1149 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1596 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1594 X0
       grind)
    | (have r₁ := eq1594 X0
       have r₂ := eq1550
       grind)
    | exact resolve eq1594 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq1594
  have eq1929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1596 eq113
    | exact resolve eq113 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq1596
  have eq1933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1929
  have eq1937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1933
    | exact resolve eq1933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq1939 : x = (M.op y x) := by
    first
    | (have r₁ := eq1937
       have r₂ := eq27
       grind)
    | exact resolve eq1937 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1949 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq373 X0 y x
       have i₂ := eq1939
       grind)
    | exact superpose eq1939 eq373
    | exact resolve eq373 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq1950 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq555 y x
       have i₂ := eq1939
       grind)
    | exact superpose eq1939 eq555
    | exact resolve eq555 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq2097 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq1949 eq1950
    | exact resolve eq1950 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949 eq1950
  have eq2098 : x = (M.op x x) := by
    first
    | (have i₁ := eq2097
       have i₂ := eq1939
       grind)
    | exact superpose eq1939 eq2097
    | exact resolve eq2097 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939 eq2097
  have eq2100 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2098
       grind)
    | exact superpose eq2098 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2098
       grind)
    | exact resolve eq13 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2114 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2141 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2114 x
       grind)
    | exact superpose eq2114 eq43
    | exact resolve eq43 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2142 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq2114 y
       grind)
    | exact superpose eq2114 eq76
    | exact resolve eq76 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2114
  have eq2148 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2142
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2142
    | exact resolve eq2142 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2142
  have eq2149 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2141
       have i₂ := eq2098
       grind)
    | exact superpose eq2098 eq2141
    | exact resolve eq2141 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098 eq2141
  have eq2151 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq2148
    | exact resolve eq2148 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2148
  have eq2152 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2149
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2149
    | exact resolve eq2149 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2149
  have eq2169 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2152 eq79
    | (have j0 := eq79 (σ x) (σ x)
       grind)
    | exact resolve eq79 eq2152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2152
  have eq2170 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2169
  have eq2232 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq2170 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq2170
       grind)
    | exact resolve eq13 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq2247 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2247 eq2151
    | exact resolve eq2151 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq2247
  have eq2575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2568
    | exact resolve eq2568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2568
  have eq2583 : False := by grind
  exact eq2583

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X0 X1) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq51
    | (have j0 := eq51 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq51 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq297
       have i₂ := eq51 y x
       grind)
    | exact superpose eq51 eq297
    | (have j1 := eq51 (σ x) (σ y)
       grind)
    | (have r₁ := eq297
       have r₂ := eq51 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq297
       have r₂ := eq51 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq297 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq297
  have eq332 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq327
  have eq419 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332
       grind)
    | exact superpose eq332 eq16
    | exact resolve eq16 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq612 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq40 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq613 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq612
    | exact resolve eq612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq617 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq613 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq613
    | exact resolve eq613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq643 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq617
    | exact resolve eq617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq706 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq643 X0
       grind)
    | exact superpose eq643 eq433
    | exact resolve eq433 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq643
  have eq6016 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq419
       have r₂ := eq706 x
       grind)
    | exact resolve eq419 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq6018 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6016
       grind)
    | exact superpose eq6016 eq10
    | exact resolve eq10 eq6016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6016
  have eq6055 : x = y := by
    first
    | (have i₁ := eq6018
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6018
    | exact resolve eq6018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq6057 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6055
       grind)
    | exact superpose eq6055 eq16
    | exact resolve eq16 eq6055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6055
  have eq6058 : False := by grind
  exact eq6058

/-- `Equation4646`: `(x ◇ y) ◇ x = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_pxx_pyx_Equation4646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X1) := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X3 X1)
       have i₂ := eq16 X3 X1 X0
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X2 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq190 : (M.op (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 X1) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op y X1)
       have i₂ := eq16 y X1 X0
       grind)
    | (have i₁ := eq175 (M.op x y)
       have i₂ := eq16 X0 y x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op (M.op X1 y) y) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) y X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq199 X0 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq199
    | exact resolve eq199 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq199
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X0 X1) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op sF3 X1)
       have i₂ := eq16 sF3 X1 x
       grind)
    | (have i₁ := eq176 (M.op x sF3)
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq176 eq218
    | exact resolve eq218 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq218
  have eq241 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op x y) y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) X0 X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X0 y)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq190 eq241
    | exact resolve eq241 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq253 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq200 eq245
    | exact resolve eq245 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq257 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) (M.op (σ y) y)) := by
    first
    | (have i₁ := eq182 (M.op sF3 y)
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq274 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq212 eq270
    | exact resolve eq270 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq275 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq212 eq269
    | exact resolve eq269 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq281 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) x) (M.op (σ y) y)) := by
    first
    | exact superpose eq190 eq257
    | exact resolve eq257 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq284 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq219 eq274
    | exact resolve eq274 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq285 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq275 X0 x
       have i₂ := eq253 X0 x
       grind)
    | exact superpose eq253 eq275
    | exact resolve eq275 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq286 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq200 eq281
    | exact resolve eq281 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq281
  have eq289 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq190 eq284
    | exact resolve eq284 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq284
  have eq412 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq253 X1 x
       grind)
    | exact superpose eq253 eq16
    | exact resolve eq16 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq449 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq460 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq174
  have eq609 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq3999 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq609
       grind)
    | exact superpose eq609 eq39
    | exact resolve eq39 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq4000 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3999
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3999
    | exact resolve eq3999 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3999
  have eq4002 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq4000
    | exact resolve eq4000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq5146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4002 eq611
    | exact resolve eq611 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4002
  have eq5153 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq5146
       have r₂ := eq27
       grind)
    | exact resolve eq5146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5158 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5153 eq460
    | exact resolve eq460 eq5153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq5153
  have eq5206 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq5158
    | exact resolve eq5158 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq5223 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq5206
       have r₂ := eq13 y x
       grind)
    | exact resolve eq5206 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq5238 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq609
       have i₂ := eq5223
       grind)
    | exact superpose eq5223 eq609
    | exact resolve eq609 eq5223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq5239 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq5223
       grind)
    | exact superpose eq5223 eq36
    | exact resolve eq36 eq5223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5223
  have eq5241 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5238
  have eq5244 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5239
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5239
    | exact resolve eq5239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239
  have eq5263 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 y y X0 X1
       have i₂ := eq5241
       grind)
    | exact superpose eq5241 eq183
    | exact resolve eq183 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq5272 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq412 y y
       have i₂ := eq5241
       grind)
    | exact superpose eq5241 eq412
    | exact resolve eq412 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq5275 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5272
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5272
    | exact resolve eq5272 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5272
  have eq5281 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5263 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5263
    | (have j0 := eq5263 X0 X1
       grind)
    | exact resolve eq5263 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq5298 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq5281 x X1
       have i₂ := eq412 x X1
       grind)
    | (have i₁ := eq5281 x y
       have i₂ := eq412 x X1
       grind)
    | exact superpose eq412 eq5281
    | exact resolve eq5281 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5281
  have eq5309 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq5275 eq5298
    | exact resolve eq5298 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5298
  have eq5315 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5244 eq611
    | exact resolve eq611 eq5244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq5244
  have eq5319 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5315
  have eq5473 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5309 eq189
    | exact resolve eq189 eq5309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq5529 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5473
    | exact resolve eq5473 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5473
  have eq5589 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5319 eq412
    | exact resolve eq412 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq5592 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5589
    | exact resolve eq5589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5589
  have eq5613 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5275 eq5592
    | exact resolve eq5592 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5592
  have eq5659 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5613 eq212
    | exact resolve eq212 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5665 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5613 eq286
    | exact resolve eq286 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq5668 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq5669 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5665
    | exact resolve eq5665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5665
  have eq5675 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5659
    | exact resolve eq5659 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5677 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5613 eq5669
    | exact resolve eq5669 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669
  have eq5680 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5613 eq5675
    | exact resolve eq5675 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5613 eq5675
  have eq5690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5529 eq663
    | (have j0 := eq663 (σ (M.op x y))
       grind)
    | (have r₁ := eq663 (σ (M.op x y))
       have r₂ := eq5529
       grind)
    | exact resolve eq663 eq5529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529
  have eq5691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5690
  have eq5776 : (τ (σ x)) = (k x (τ (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5680 eq449
    | exact resolve eq449 eq5680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq5680
  have eq5808 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5776
    | exact resolve eq5776 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776
  have eq5832 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5691 eq412
    | exact resolve eq412 eq5691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5834 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5275 eq5832
    | exact resolve eq5832 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275 eq5832
  have eq6049 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq663 x
       have i₂ := eq5808
       grind)
    | exact superpose eq5808 eq663
    | (have j0 := eq663 x
       grind)
    | (have r₁ := eq663 x
       have r₂ := eq5808
       grind)
    | exact resolve eq663 eq5808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq5808
  have eq6050 : x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6049
  have eq6055 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5834 eq5691
    | exact resolve eq5691 eq5834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691 eq5834
  have eq6078 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq6055
  have eq7560 : (M.op (M.op x y) x) = (M.op (M.op x x) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq191 x x
       have i₂ := eq6050
       grind)
    | exact superpose eq6050 eq191
    | exact resolve eq191 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq7572 : (σ x) = (M.op (M.op x x) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5677 eq7560
    | exact resolve eq7560 eq5677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5677 eq7560
  have eq7588 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6050 eq7572
    | exact resolve eq7572 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050 eq7572
  have eq7599 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7588
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7588
    | exact resolve eq7588 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588
  have eq7603 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7599
       have r₂ := eq5668
       grind)
    | exact resolve eq7599 eq5668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668 eq7599
  have eq7606 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7603 eq27
    | exact resolve eq27 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7608 : (M.op (M.op x y) (σ y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7603 eq212
    | exact resolve eq212 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq7615 : (M.op (M.op x y) x) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7603 eq289
    | exact resolve eq289 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7617 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7603 eq6078
    | exact resolve eq6078 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6078
  have eq7618 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq7617
  have eq7635 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq7618 eq26
    | exact resolve eq26 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7636 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq7618 eq29
    | exact resolve eq29 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq7648 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7618 eq219
    | exact resolve eq219 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq7652 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7618 eq285
    | exact resolve eq285 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq7618
  have eq7677 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7652 X0
       grind)
    | (have r₁ := eq7652 X0
       have r₂ := eq7606
       grind)
    | exact resolve eq7652 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7652
  have eq7681 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7648 X0
       grind)
    | (have r₁ := eq7648 X0
       have r₂ := eq7606
       grind)
    | exact resolve eq7648 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7648
  have eq7693 : x = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7636
       have r₂ := eq7606
       grind)
    | exact resolve eq7636 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7636
  have eq7694 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7635
       have r₂ := eq7606
       grind)
    | exact resolve eq7635 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7635
  have eq7696 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7603 eq7677
    | exact resolve eq7677 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7677
  have eq7700 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7603 eq7681
    | exact resolve eq7681 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7681
  have eq7708 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7603 eq7694
    | exact resolve eq7694 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603 eq7694
  have eq7709 : ∀ X0 : G, (M.op (M.op x y) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7615 eq7696
    | exact resolve eq7696 eq7615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq7713 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7700 eq7709
    | exact resolve eq7709 eq7700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7700 eq7709
  have eq7721 : (σ x) = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq14
    | exact resolve eq14 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq7722 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7721
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7721
    | exact resolve eq7721 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7721
  have eq7868 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7608 eq7708
    | exact resolve eq7708 eq7608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7608 eq7708
  have eq7897 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7868
  have eq7922 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7722 eq7897
    | exact resolve eq7897 eq7722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7722 eq7897
  have eq7946 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7922 eq189
    | exact resolve eq189 eq7922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7980 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7946
    | exact resolve eq7946 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7946
  have eq8007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7980 eq661
    | (have j0 := eq661 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq661 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq7980
       grind)
    | exact resolve eq661 eq7980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7980
  have eq8008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8007
  have eq8009 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8008
  have eq8039 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8009 eq412
    | exact resolve eq412 eq8009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8045 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7615 eq8039
    | exact resolve eq8039 eq7615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7615 eq8039
  have eq8063 : (M.op (M.op x y) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7713 eq8045
    | exact resolve eq8045 eq7713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713 eq8045
  have eq8079 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7922 eq8063
    | exact resolve eq8063 eq7922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7922 eq8063
  have eq8114 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8079 eq8009
    | exact resolve eq8009 eq8079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009 eq8079
  have eq8141 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq8114
  have eq8164 : x = (M.op x y) := by
    first
    | (have r₁ := eq8141
       have r₂ := eq7606
       grind)
    | exact resolve eq8141 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606 eq8141
  have eq8183 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8164
       grind)
    | exact superpose eq8164 eq18
    | exact resolve eq18 eq8164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8184 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq8164
       grind)
    | exact superpose eq8164 eq22
    | exact resolve eq22 eq8164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq8206 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8184 eq20
    | exact resolve eq20 eq8184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8184
  have eq8284 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8183 eq181
    | exact resolve eq181 eq8183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq8183
  have eq8333 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8284 eq189
    | exact resolve eq189 eq8284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq8366 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq8333
    | exact resolve eq8333 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8333
  have eq8377 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq8206 eq8366
    | exact resolve eq8366 eq8206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8366
  have eq8405 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8377 eq661
    | (have j0 := eq661 (σ x) (σ x)
       grind)
    | (have r₁ := eq661 (σ x) (σ x)
       have r₂ := eq8377
       grind)
    | exact resolve eq661 eq8377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq8377
  have eq8406 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8405
  have eq8407 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8406
  have eq8435 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq8407 eq209
    | exact resolve eq209 eq8407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq8439 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8407 eq412
    | exact resolve eq412 eq8407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq8441 : (σ x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq8407 eq8439
    | exact resolve eq8439 eq8407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq8445 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq8407 eq8435
    | exact resolve eq8435 eq8407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8407 eq8435
  have eq8458 : (σ x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8441
       have i₂ := eq8164
       grind)
    | exact superpose eq8164 eq8441
    | exact resolve eq8441 eq8164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441
  have eq8462 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq289 eq8445
    | exact resolve eq8445 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq8445
  have eq8475 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq8284 eq8458
    | exact resolve eq8458 eq8284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq8479 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8462
       have i₂ := eq8164
       grind)
    | exact superpose eq8164 eq8462
    | exact resolve eq8462 eq8164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8164 eq8462
  have eq8492 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8284 eq8479
    | exact resolve eq8479 eq8284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8284 eq8479
  have eq8503 : (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq8475 eq8492
    | exact resolve eq8492 eq8475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8492
  have eq8507 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq8475 eq26
    | exact resolve eq26 eq8475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8558 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8503 eq8507
    | exact resolve eq8507 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8503 eq8507
  have eq8585 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq8558 eq27
    | exact resolve eq27 eq8558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8558
  have eq8606 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq8206 eq8585
    | exact resolve eq8585 eq8206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8206 eq8585
  have eq8610 : False := by grind
  exact eq8610

/-- `Equation4646`: `(x ◇ y) ◇ x = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pyx_Equation4646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X1) := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X3 X1)
       have i₂ := eq16 X3 X1 X0
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X2 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 X1) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op y X1)
       have i₂ := eq16 y X1 X0
       grind)
    | (have i₁ := eq175 (M.op x y)
       have i₂ := eq16 X0 y x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op (M.op X1 y) y) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) y X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq199 X0 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq199
    | exact resolve eq199 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq199
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X0 X1) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op sF3 X1)
       have i₂ := eq16 sF3 X1 x
       grind)
    | (have i₁ := eq176 (M.op x sF3)
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq176 eq218
    | exact resolve eq218 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq218
  have eq241 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op x y) y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) X0 X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X0 y)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq190 eq241
    | exact resolve eq241 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq253 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq200 eq245
    | exact resolve eq245 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq257 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) (M.op (σ y) y)) := by
    first
    | (have i₁ := eq182 (M.op sF3 y)
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq182
  have eq274 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq212 eq270
    | exact resolve eq270 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq270
  have eq281 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) x) (M.op (σ y) y)) := by
    first
    | exact superpose eq190 eq257
    | exact resolve eq257 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq284 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq219 eq274
    | exact resolve eq274 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq274
  have eq286 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq200 eq281
    | exact resolve eq281 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq281
  have eq289 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq190 eq284
    | exact resolve eq284 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq391 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq253 X0 (M.op X0 y)
       have i₂ := eq197 X0
       grind)
    | (have i₁ := eq253 x (M.op x y)
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq253
    | exact resolve eq253 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq412 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq253 X1 x
       grind)
    | exact superpose eq253 eq16
    | exact resolve eq16 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq460 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq579 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq391 eq174
    | exact resolve eq174 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq696 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1 x
       have i₂ := eq253 X0 x
       grind)
    | exact superpose eq253 eq627
    | (have j0 := eq627 X1 X1 x
       grind)
    | exact resolve eq627 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq627
  have eq911 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq671 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq671
    | (have j0 := eq671 (σ X0)
       grind)
    | exact resolve eq671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq39
    | exact resolve eq39 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq7015 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7014
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7014
    | exact resolve eq7014 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7014
  have eq7017 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq7015
    | exact resolve eq7015 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7015
  have eq11484 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq696 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq696
    | (have j0 := eq696 (σ X1) (σ X1)
       grind)
    | exact resolve eq696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq20576 : (σ (M.op (M.op x y) x)) ≠ (σ (M.op (M.op x y) x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq579 eq911
    | (have j0 := eq911 (M.op (M.op x y) x)
       grind)
    | exact resolve eq911 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq20612 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by grind
  clear eq20576
  have eq20738 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq20612 eq183
    | exact resolve eq183 eq20612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20762 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ (M.op (M.op x y) x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq20612 eq20738
    | exact resolve eq20738 eq20612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20738
  have eq20780 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (σ (M.op (M.op x y) x)) X1) := by
    intro X1
    first
    | (have i₁ := eq20762 x X1
       have i₂ := eq412 x X1
       grind)
    | (have i₁ := eq20762 x y
       have i₂ := eq412 x X1
       grind)
    | exact superpose eq412 eq20762
    | exact resolve eq20762 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20762
  have eq20909 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq20780 eq20612
    | exact resolve eq20612 eq20780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7017 eq662
    | exact resolve eq662 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq7017
  have eq22092 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22084
       have r₂ := eq27
       grind)
    | exact resolve eq22084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22084
  have eq22099 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22092 eq460
    | exact resolve eq460 eq22092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq22092
  have eq22152 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq22099
    | exact resolve eq22099 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22099
  have eq22172 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq22152
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq22152
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq22152
       have r₂ := eq13 y x
       grind)
    | exact resolve eq22152 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22152
  have eq22190 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22172 eq449
    | exact resolve eq449 eq22172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq22172
  have eq22230 : x = (k x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq22190
    | exact resolve eq22190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22190
  have eq22246 : x = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq22230
       have r₂ := eq13 x x
       grind)
    | exact resolve eq22230 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22230
  have eq22252 : x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22246
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq22246
    | exact resolve eq22246 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22255 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq653
       have i₂ := eq22246
       grind)
    | exact superpose eq22246 eq653
    | exact resolve eq653 eq22246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq22262 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq671 x
       grind)
    | (have r₁ := eq22255
       have r₂ := eq671 x
       grind)
    | exact resolve eq22255 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq22255
  have eq22265 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq22252
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq22252
       have r₂ := eq13 y x
       grind)
    | exact resolve eq22252 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22252
  have eq22300 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22262
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq22262
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq22262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22310 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq22262
       grind)
    | exact superpose eq22262 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq22262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22328 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq412 y y
       have i₂ := eq22262
       grind)
    | exact superpose eq22262 eq412
    | exact resolve eq412 eq22262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22262
  have eq22329 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq22310
  have eq22330 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq22300
  have eq22331 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22328
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22328
    | exact resolve eq22328 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22328
  have eq22351 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22329 eq22330
    | exact resolve eq22330 eq22329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22329 eq22330
  have eq22352 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq22351
  have eq22380 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq911 x
       have i₂ := eq22265
       grind)
    | exact superpose eq22265 eq911
    | (have j0 := eq911 x
       grind)
    | exact resolve eq911 eq22265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22265
  have eq22389 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq22380
  have eq22390 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22389
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22389
    | exact resolve eq22389 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22389
  have eq22837 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22331 eq20909
    | exact resolve eq20909 eq22331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20909
  have eq22883 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22837
    | exact resolve eq22837 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22837
  have eq22930 : (M.op (M.op x y) x) = (M.op (M.op x x) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq191 x x
       have i₂ := eq22883
       grind)
    | exact superpose eq22883 eq191
    | exact resolve eq191 eq22883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22935 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq412 x x
       have i₂ := eq22883
       grind)
    | exact superpose eq22883 eq412
    | exact resolve eq412 eq22883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22938 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22883 eq22935
    | exact resolve eq22935 eq22883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22935
  have eq22943 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22883 eq22930
    | exact resolve eq22930 eq22883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22883 eq22930
  have eq22958 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22943
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22943
    | exact resolve eq22943 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22943
  have eq23443 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22958 eq22938
    | exact resolve eq22938 eq22958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22938 eq22958
  have eq23465 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq23443
  have eq24206 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq22352
       grind)
    | exact superpose eq22352 eq40
    | exact resolve eq40 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq24220 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24206
    | exact resolve eq24206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24206
  have eq24227 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24220
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24220
    | exact resolve eq24220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24220
  have eq24488 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22390 eq209
    | exact resolve eq209 eq22390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24492 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22390 eq412
    | exact resolve eq412 eq22390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24495 : (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22390 eq24492
    | exact resolve eq24492 eq22390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24492
  have eq24499 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq289 eq24488
    | exact resolve eq24488 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24488
  have eq24515 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22390 eq24499
    | exact resolve eq24499 eq22390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22390 eq24499
  have eq24527 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq24515
    | exact resolve eq24515 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24515
  have eq24531 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24495 eq24527
    | exact resolve eq24527 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24495 eq24527
  have eq24551 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 y y X0 X1
       have i₂ := eq24531
       grind)
    | exact superpose eq24531 eq183
    | exact resolve eq183 eq24531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq24560 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq412 y y
       have i₂ := eq24531
       grind)
    | exact superpose eq24531 eq412
    | exact resolve eq412 eq24531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24531
  have eq24563 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24560
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24560
    | exact resolve eq24560 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24560
  have eq24569 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq24551 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24551
    | (have j0 := eq24551 X0 X1
       grind)
    | exact resolve eq24551 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24551
  have eq24588 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq24569 x X1
       have i₂ := eq412 x X1
       grind)
    | (have i₁ := eq24569 x y
       have i₂ := eq412 x X1
       grind)
    | exact superpose eq412 eq24569
    | exact resolve eq24569 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24569
  have eq24601 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq24563 eq24588
    | exact resolve eq24588 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563 eq24588
  have eq26834 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11484 y y
       have i₂ := eq22352
       grind)
    | exact superpose eq22352 eq11484
    | (have j0 := eq11484 y y
       grind)
    | exact resolve eq11484 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11484 eq22352
  have eq26965 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq26834
  have eq27042 : (M.op (M.op x y) x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26965
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26965
    | exact resolve eq26965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26965
  have eq27111 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27042
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27042
    | exact resolve eq27042 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27042
  have eq27155 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq27111
    | exact resolve eq27111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27111
  have eq27189 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27155
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27155
    | exact resolve eq27155 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27155
  have eq27221 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22331 eq27189
    | exact resolve eq27189 eq22331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22331 eq27189
  have eq40193 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27221 eq174
    | exact resolve eq174 eq27221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27221
  have eq40232 : x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24227 eq40193
    | exact resolve eq40193 eq24227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24227 eq40193
  have eq40302 : (M.op (M.op x y) x) = (M.op (M.op x x) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq191 x x
       have i₂ := eq40232
       grind)
    | exact superpose eq40232 eq191
    | exact resolve eq191 eq40232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq40307 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq412 x x
       have i₂ := eq40232
       grind)
    | exact superpose eq40232 eq412
    | exact resolve eq412 eq40232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40310 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40232 eq40307
    | exact resolve eq40307 eq40232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40307
  have eq40315 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40232 eq40302
    | exact resolve eq40302 eq40232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40232 eq40302
  have eq40330 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40315
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40315
    | exact resolve eq40315 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40315
  have eq40517 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40310 eq24601
    | exact resolve eq24601 eq40310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24601 eq40310
  have eq40561 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq40517
  have eq40895 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40561 eq286
    | exact resolve eq286 eq40561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq40898 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  have eq40900 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq40895
    | exact resolve eq40895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40895
  have eq40910 : (σ x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40561 eq40900
    | exact resolve eq40900 eq40561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40561 eq40900
  have eq40916 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40330 eq40910
    | exact resolve eq40910 eq40330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40330 eq40910
  have eq40921 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40916
       have r₂ := eq40898
       grind)
    | exact resolve eq40916 eq40898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40898 eq40916
  have eq40925 : y = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40921 eq31
    | exact resolve eq31 eq40921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq40921
  have eq41113 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq40925
    | exact resolve eq40925 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40925
  have eq41117 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq41113 eq27
    | exact resolve eq27 eq41113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41113
  have eq41138 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq41117
       have r₂ := eq23465
       grind)
    | exact resolve eq41117 eq23465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23465 eq41117
  have eq41140 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq41138
       grind)
    | exact superpose eq41138 eq18
    | exact resolve eq18 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41141 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq41138
       grind)
    | exact superpose eq41138 eq22
    | exact resolve eq22 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41256 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq41141
    | exact resolve eq41141 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41141
  have eq41257 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq190 eq41140
    | exact resolve eq41140 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq41140
  have eq41269 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq41138 eq41257
    | exact resolve eq41257 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41257
  have eq41387 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq41269 eq174
    | exact resolve eq174 eq41269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq41451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq41387 eq911
    | (have j0 := eq911 (M.op x y)
       grind)
    | exact resolve eq911 eq41387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq41387
  have eq41461 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq41451
  have eq41467 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq41461
    | exact resolve eq41461 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41461
  have eq41475 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq41256 eq41467
    | exact resolve eq41467 eq41256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41467
  have eq41542 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq41475 eq209
    | exact resolve eq209 eq41475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq41546 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq41475 eq412
    | exact resolve eq412 eq41475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq41549 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq41138 eq41546
    | exact resolve eq41546 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41546
  have eq41553 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq289 eq41542
    | exact resolve eq41542 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq41542
  have eq41568 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq41269 eq41549
    | exact resolve eq41549 eq41269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41549
  have eq41572 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq41138 eq41553
    | exact resolve eq41553 eq41138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41138 eq41553
  have eq41588 : (M.op x y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq41269 eq41572
    | exact resolve eq41572 eq41269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41269 eq41572
  have eq41599 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq41475 eq41588
    | exact resolve eq41588 eq41475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41588
  have eq41603 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq41599
    | exact resolve eq41599 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41599
  have eq41606 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq41603 eq27
    | exact resolve eq27 eq41603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41603
  have eq41638 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq41256 eq41606
    | exact resolve eq41606 eq41256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41256 eq41606
  have eq41644 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq41638
  have eq41667 : (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq41568 eq41475
    | exact resolve eq41475 eq41568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41475 eq41568
  have eq41696 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq41667
  have eq41719 : x = y := by
    first
    | (have r₁ := eq41696
       have r₂ := eq41644
       grind)
    | exact resolve eq41696 eq41644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41644 eq41696
  have eq41752 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq41719
       grind)
    | exact superpose eq41719 eq18
    | exact resolve eq18 eq41719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq41787 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq22246
       have i₂ := eq41719
       grind)
    | exact superpose eq41719 eq22246
    | exact resolve eq22246 eq41719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22246 eq41719
  have eq41832 : x = (k x x) := by grind
  clear eq41787
  have eq42083 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq41752
       grind)
    | exact superpose eq41752 eq11
    | exact resolve eq11 eq41752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42100 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq42083
  have eq42116 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42100
       have i₂ := eq41832
       grind)
    | exact superpose eq41832 eq42100
    | exact resolve eq42100 eq41832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41832 eq42100
  have eq42117 : x = (M.op x y) := by grind
  clear eq42116
  have eq42121 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq42117
       grind)
    | exact superpose eq42117 eq22
    | exact resolve eq22 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq42134 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq42117
       grind)
    | exact superpose eq42117 eq391
    | exact resolve eq391 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq42159 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq20612
       have i₂ := eq42117
       grind)
    | exact superpose eq42117 eq20612
    | exact resolve eq20612 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20612
  have eq42164 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq20780 x
       have i₂ := eq42117
       grind)
    | exact superpose eq42117 eq20780
    | exact resolve eq20780 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20780
  have eq42191 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41752
       have i₂ := eq42117
       grind)
    | exact superpose eq42117 eq41752
    | exact resolve eq41752 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41752 eq42117
  have eq42211 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq42191 eq42164
    | exact resolve eq42164 eq42191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42164
  have eq42216 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42191 eq42159
    | exact resolve eq42159 eq42191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42159
  have eq42233 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq42191 eq42134
    | exact resolve eq42134 eq42191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42134 eq42191
  have eq42248 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq42211
    | (have j0 := eq42211 X0
       grind)
    | exact resolve eq42211 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42211
  have eq42253 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq42216
    | exact resolve eq42216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42216
  have eq42274 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq42248 eq42253
    | exact resolve eq42253 eq42248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42248 eq42253
  have eq42439 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42121 eq20
    | exact resolve eq20 eq42121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42121
  have eq42601 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq42274 eq42439
    | exact resolve eq42439 eq42274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42439
  have eq43717 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq42601 eq26
    | exact resolve eq26 eq42601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq42601
  have eq43901 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42233 eq43717
    | exact resolve eq43717 eq42233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42233 eq43717
  have eq44008 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq43901 eq27
    | exact resolve eq27 eq43901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43901
  have eq44029 : False := by grind
  exact eq44029

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pxx_pxy_Equation575 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (M.op X0 X1)))) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (M.op X0 X1)))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq30 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X0 X1 x
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq55
    | exact resolve eq55 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq55
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq49 (σ X1) (σ X0)
       grind)
    | exact superpose eq49 eq15
    | (have j1 := eq49 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq79
    | (have j0 := eq79 X0 X1
       have j1 := eq49 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq79 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq79
  have eq67100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1280 x y
       grind)
    | exact superpose eq1280 eq16
    | (have j1 := eq1280 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1280 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1280 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1280 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq67149 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq67100
  have eq72539 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67149
       grind)
    | exact superpose eq67149 eq10
    | exact resolve eq10 eq67149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67149
  have eq72684 : x = y ∨ x = y := by
    first
    | (have i₁ := eq72539
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq72539
    | exact resolve eq72539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72539
  have eq72685 : x = y := by grind
  clear eq72684
  have eq92634 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72685
       grind)
    | exact superpose eq72685 eq16
    | exact resolve eq16 eq72685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72685
  have eq92647 : False := by grind
  exact eq92647
