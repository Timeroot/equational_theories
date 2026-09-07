import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pxx_pxy_Equation3583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq22 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq259 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq260 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq259
    | exact resolve eq259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq259
  have eq435 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq260 (σ X1) (σ X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq260
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq260 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq49 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq442 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq459 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq435 X0 X1
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq435 X0 X1
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq435 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq480 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq459
    | (have j0 := eq459 X0 X1
       grind)
    | exact resolve eq459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq830 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq442 (M.op X0 X1)
       have i₂ := eq260 X0 X1
       grind)
    | exact superpose eq260 eq442
    | (have j0 := eq442 (M.op X0 X1)
       grind)
    | exact resolve eq442 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq835 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq1322 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq835 X0 X1
       grind)
    | exact superpose eq835 eq22
    | exact resolve eq22 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq22499 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq480 (τ X0) X1
       grind)
    | exact superpose eq480 eq18
    | (have j1 := eq480 (τ X0) X1
       grind)
    | exact resolve eq18 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22502 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq480 X0 X1
       grind)
    | exact superpose eq480 eq10
    | (have j1 := eq480 X0 X1
       grind)
    | exact resolve eq10 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq22779 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22502 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22502
    | (have j0 := eq22502 X0 X1
       grind)
    | exact resolve eq22502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22502
  have eq22784 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22499 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22499
    | (have j0 := eq22499 X0 X1
       grind)
    | exact resolve eq22499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499
  have eq22829 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22784 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22784
    | (have j0 := eq22784 X0 X1
       grind)
    | exact resolve eq22784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22784
  have eq22844 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22829 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq22829
    | (have j0 := eq22829 X0 X1
       grind)
    | exact resolve eq22829 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq22829
  have eq22859 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22844 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22844
    | (have j0 := eq22844 X1 X1
       grind)
    | exact resolve eq22844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22844
  have eq23591 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq22859 X1 X0
       grind)
    | exact superpose eq22859 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq22859 X1 X0
       grind)
    | exact resolve eq14 eq22859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22859
  have eq23681 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq23591 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23591
  have eq24087 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X0 x
       have i₂ := eq23681 X0 X1
       grind)
    | exact superpose eq23681 eq22
    | (have j1 := eq23681 X0 X2
       grind)
    | exact resolve eq22 eq23681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22779 y x
       grind)
    | exact superpose eq22779 eq16
    | (have j1 := eq22779 y x
       grind)
    | exact resolve eq16 eq22779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22779
  have eq47269 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq46600
       have i₂ := eq24087 y X0 x
       grind)
    | exact superpose eq24087 eq46600
    | (have j1 := eq24087 y X0 x
       grind)
    | exact resolve eq46600 eq24087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24087 eq46600
  have eq47277 : ∀ X0 : G, y = (k y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq47269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47269
  have eq49370 : y = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq260 x y
       have i₂ := eq47277 x
       grind)
    | exact superpose eq47277 eq260
    | exact resolve eq260 eq47277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq47277
  have eq49457 : y = (k y y) := by grind
  clear eq49370
  have eq49987 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23681 y y
       have i₂ := eq49457
       grind)
    | exact superpose eq49457 eq23681
    | (have j0 := eq23681 y x
       grind)
    | exact resolve eq23681 eq49457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23681 eq49457
  have eq49990 : y = (M.op y y) := by grind
  clear eq49987
  have eq50726 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22 y y x
       have i₂ := eq49990
       grind)
    | exact superpose eq49990 eq22
    | exact resolve eq22 eq49990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq50744 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1322 y y x
       have i₂ := eq49990
       grind)
    | exact superpose eq49990 eq1322
    | exact resolve eq1322 eq49990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq49990
  have eq53731 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50744 (σ x)
       grind)
    | exact superpose eq50744 eq16
    | exact resolve eq16 eq50744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50744
  have eq53747 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq53731
       have i₂ := eq50726 x
       grind)
    | exact superpose eq50726 eq53731
    | exact resolve eq53731 eq50726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50726 eq53731
  have eq53748 : False := by grind
  exact eq53748

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_x_pxy_Equation3583 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq25 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq26 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq62 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq66 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq67
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26
    | exact resolve eq26 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq60 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq60 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq229 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq230 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq230
    | (have j0 := eq230 X0 X1
       grind)
    | exact resolve eq230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq247 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq248 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (k (M.op X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 (M.op X0 X1) X1
       have i₂ := eq26 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq86
    | exact resolve eq86 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1114 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq236
    | exact resolve eq236 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq1163 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (k (M.op (τ X0) (τ X0)) X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 X0 X1
       have i₂ := eq30 X0 (σ X1)
       grind)
    | exact superpose eq30 eq1114
    | (have j0 := eq1114 X0 X1
       grind)
    | exact resolve eq1114 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1168 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1163 X0 X1
       have i₂ := eq248 X0 X1
       grind)
    | exact superpose eq248 eq1163
    | (have j0 := eq1163 X0 X1
       grind)
    | exact resolve eq1163 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1171 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1168 X0 X1
       have i₂ := eq248 X0 X1
       grind)
    | exact superpose eq248 eq1168
    | (have j0 := eq1168 X0 X1
       grind)
    | exact resolve eq1168 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1616 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) ≠ (M.op (σ X1) (M.op X0 X0)) ∨ (σ (k (M.op (τ X0) (τ X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq226
    | exact resolve eq226 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq226
  have eq1643 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (M.op (τ X0) (τ X0)) X1)) ∨ (σ (k (M.op (τ X0) (τ X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1616 X0 X1
       have i₂ := eq26 X0 X0 (σ X1)
       grind)
    | exact superpose eq26 eq1616
    | (have j0 := eq1616 X0 X1
       grind)
    | exact resolve eq1616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1651 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) (σ X1)) ∨ (σ (k (M.op (τ X0) (τ X0)) X1)) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1643 X0 X1
       have i₂ := eq248 X0 X1
       grind)
    | exact superpose eq248 eq1643
    | (have j0 := eq1643 X0 X1
       grind)
    | exact resolve eq1643 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1659 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (k (M.op (τ X0) (τ X0)) X1)) ∨ (M.op X0 X0) ≠ (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1651 X0 X1
       have i₂ := eq30 X0 (σ X1)
       grind)
    | exact superpose eq30 eq1651
    | (have j0 := eq1651 X0 X1
       grind)
    | exact resolve eq1651 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1651
  have eq1661 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) ≠ (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1659 X0 X1
       have i₂ := eq248 X0 X1
       grind)
    | exact superpose eq248 eq1659
    | (have j0 := eq1659 X0 X1
       grind)
    | exact resolve eq1659 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1659
  have eq1663 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (k (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1661 X0 X1
       have j1 := eq1171 X0 X1
       grind)
    | (have r₁ := eq1661 (σ X1) X1
       have r₂ := eq1171 (σ X1) X1
       grind)
    | (have r₁ := eq1661 X0 X1
       have r₂ := eq1171 X0 X1
       grind)
    | exact resolve eq1661 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq1661
  have eq2755 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1663 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1663
    | exact resolve eq1663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2775 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 X0)) X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op X0 X0) X1
       have i₂ := eq1663 X0 X1
       grind)
    | exact superpose eq1663 eq66
    | (have j1 := eq1663 X0 X1
       grind)
    | exact resolve eq66 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1663
  have eq2837 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (k (τ (M.op X0 X0)) X1) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2755 X0 (τ X0)
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq2755
    | exact resolve eq2755 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq2755
  have eq86080 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2837 X0 X1
       have i₂ := eq2775 X0 X1
       grind)
    | exact superpose eq2775 eq2837
    | (have j0 := eq2837 X0 X1
       have j1 := eq2775 X0 X1
       grind)
    | exact resolve eq2837 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775 eq2837
  have eq367493 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq86080 X0 X1
       grind)
    | exact superpose eq86080 eq10
    | (have j1 := eq86080 X0 X1
       grind)
    | exact resolve eq10 eq86080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86080
  have eq367496 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq367493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367493
  have eq367518 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq367496 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq367496
    | (have j0 := eq367496 (σ X0) X1
       grind)
    | exact resolve eq367496 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq367496
  have eq367809 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq367518 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq367518
    | (have j0 := eq367518 X0 X1
       grind)
    | exact resolve eq367518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367518
  have eq367818 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367809 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq367809
    | (have j0 := eq367809 X0 X1
       grind)
    | exact resolve eq367809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367809
  have eq369005 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq367818 X0 X1
       grind)
    | exact superpose eq367818 eq11
    | (have j1 := eq367818 X0 X1
       grind)
    | exact resolve eq11 eq367818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367818
  have eq371517 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq369005 x y
       grind)
    | exact superpose eq369005 eq16
    | (have j1 := eq369005 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq369005 x y
       grind)
    | exact resolve eq16 eq369005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369005
  have eq371943 : y = (M.op x x) := by grind
  clear eq371517
  have eq373006 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq26 x x x
       have i₂ := eq371943
       grind)
    | exact superpose eq371943 eq26
    | exact resolve eq26 eq371943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq373011 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq303 x x x
       have i₂ := eq371943
       grind)
    | exact superpose eq371943 eq303
    | exact resolve eq303 eq371943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq371943
  have eq380314 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq373011 (σ x)
       grind)
    | exact superpose eq373011 eq16
    | exact resolve eq16 eq373011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373011
  have eq380478 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq380314
       have i₂ := eq373006 x
       grind)
    | exact superpose eq373006 eq380314
    | exact resolve eq380314 eq373006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373006 eq380314
  have eq380479 : False := by grind
  exact eq380479

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_x_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq22 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq12
    | (have j0 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq27 X0 X1
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 x (M.op X0 X1)
       have i₂ := eq22 X0 X1 x
       grind)
    | exact superpose eq22 eq49
    | exact resolve eq49 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq27
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq27 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq122 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X1) (σ X0) x
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq22
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq22 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq53 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq127 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq145 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op X1 (σ X0)) X0
       have i₂ := eq49 X1 (σ X0)
       grind)
    | exact superpose eq49 eq66
    | exact resolve eq66 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq157 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq151
    | exact resolve eq151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq439 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq127 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq127
    | (have j0 := eq127 (M.op X0 X1)
       grind)
    | exact resolve eq127 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq127 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq127
    | (have j0 := eq127 (τ X0)
       grind)
    | exact resolve eq127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq127
  have eq444 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq446 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq443 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq443
    | (have j0 := eq443 X0
       grind)
    | exact resolve eq443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq449 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq446 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq446
    | (have j0 := eq446 X0
       grind)
    | exact resolve eq446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq456 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq449 (τ X0)
       have i₂ := eq145 X0 X0
       grind)
    | exact superpose eq145 eq449
    | (have j0 := eq449 (τ X0)
       grind)
    | exact resolve eq449 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq592 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq627 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq641 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq444 X0 X1
       grind)
    | exact superpose eq444 eq22
    | exact resolve eq22 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq745 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 (M.op X1 X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq126
    | (have j0 := eq126 X0 (M.op X1 X0)
       grind)
    | exact resolve eq126 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq769 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq745 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq777 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq641 X1 X0 (σ X0)
       grind)
    | exact superpose eq641 eq769
    | (have j0 := eq769 X0 X1
       grind)
    | exact resolve eq769 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq855 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq122 y x X0
       grind)
    | exact superpose eq122 eq16
    | (have j1 := eq122 y x X0
       grind)
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op X2 (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq122 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1415 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq456 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq456
    | (have j0 := eq456 (M.op X0 X1)
       grind)
    | exact resolve eq456 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq456
  have eq1424 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1602 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq1424 X0 X1
       grind)
    | exact superpose eq1424 eq22
    | exact resolve eq22 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1424
  have eq8805 : ∀ X0 X1 X2 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq900 (τ X1) (τ X0) X2
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq900
    | (have j0 := eq900 (τ X1) (τ X0) X2
       grind)
    | exact resolve eq900 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq8864 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8805 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq8805
    | (have j0 := eq8805 X0 X1 X2
       grind)
    | exact resolve eq8805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8805
  have eq8887 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op X2 (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8864 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8864
    | (have j0 := eq8864 X0 X1 X2
       grind)
    | exact resolve eq8864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8864
  have eq8900 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8887 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8887
    | (have j0 := eq8887 X0 X1 X2
       grind)
    | exact resolve eq8887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887
  have eq8913 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8900 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8900
    | (have j0 := eq8900 X0 X1 X2
       grind)
    | exact resolve eq8900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8900
  have eq8914 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X1 ∨ (M.op X2 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8913 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8913
    | (have j0 := eq8913 X0 X1 X2
       grind)
    | exact resolve eq8913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8913
  have eq11586 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq855 X0
       have i₂ := eq627 y x
       grind)
    | exact superpose eq627 eq855
    | (have j0 := eq855 X0
       have j1 := eq627 y x
       grind)
    | (have r₁ := eq855 X0
       have r₂ := eq627 y x
       grind)
    | exact resolve eq855 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq855
  have eq11587 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq11586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11586
  have eq16815 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ X1) (τ X0)
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq116
    | (have j0 := eq116 (τ X0) (τ X1)
       grind)
    | exact resolve eq116 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq145
  have eq17023 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16815 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16815
    | (have j0 := eq16815 X0 X1
       grind)
    | exact resolve eq16815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16815
  have eq17070 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17023 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17023
    | (have j0 := eq17023 X0 X1
       grind)
    | exact resolve eq17023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17023
  have eq17104 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17070 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17070
    | (have j0 := eq17070 X0 X1
       grind)
    | exact resolve eq17070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17070
  have eq17134 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17104 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17104
    | (have j0 := eq17104 X0 X1
       grind)
    | exact resolve eq17104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17104
  have eq17149 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17134 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17134
    | (have j0 := eq17134 X0 X1
       grind)
    | exact resolve eq17134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17134
  have eq17156 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17149 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17149
    | (have j0 := eq17149 X0 X1
       grind)
    | exact resolve eq17149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17149
  have eq177061 : ∀ X0 X1 : G, (k (k X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (k X0 X1) X0
       have i₂ := eq17156 X0 X1
       grind)
    | exact superpose eq17156 eq49
    | (have j1 := eq17156 X0 X1
       grind)
    | exact resolve eq49 eq17156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq17156
  have eq197722 : ∀ X0 : G, y = (k (τ (σ x)) y) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq157 y (σ x)
       have i₂ := eq11587 X0
       grind)
    | exact superpose eq11587 eq157
    | (have j1 := eq11587 X0
       grind)
    | exact resolve eq157 eq11587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq11587
  have eq197793 : ∀ X0 : G, y = (k x y) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq197722 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq197722
    | (have j0 := eq197722 X0
       grind)
    | exact resolve eq197722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197722
  have eq197796 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq197793 X0
       have j1 := eq12 x y
       grind)
    | (have r₁ := eq197793 (σ y)
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq197793 X0
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq197793 X0
       have r₂ := eq12 y x
       grind)
    | exact resolve eq197793 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197793
  have eq197884 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ y = (k x y) ∨ y = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq1602 x (σ y) x
       have i₂ := eq197796 x
       grind)
    | exact superpose eq197796 eq1602
    | exact resolve eq1602 eq197796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq197796
  have eq197978 : ∀ X1 : G, y = (k x y) ∨ y = (M.op X1 y) ∨ y = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq197884 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq197884
    | exact resolve eq197884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197884
  have eq198123 : ∀ X0 : G, x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq177061 x y
       have i₂ := eq197978 X0
       grind)
    | exact superpose eq197978 eq177061
    | (have j0 := eq177061 x y
       have j1 := eq197978 X0
       grind)
    | exact resolve eq177061 eq197978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177061 eq197978
  have eq198225 : ∀ X0 : G, x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq198123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198123
  have eq198271 : ∀ X0 : G, x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq198225 X0
       have j1 := eq12 y x
       grind)
    | (have r₁ := eq198225 X0
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq198225 X0
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq198225 y
       have r₂ := eq12 y y
       grind)
    | exact resolve eq198225 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198225
  have eq198279 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq198271 X0
       have j1 := eq8914 y x X0
       grind)
    | (have r₁ := eq198271 X0
       have r₂ := eq8914 y x x
       grind)
    | exact resolve eq198271 eq8914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8914 eq198271
  have eq198472 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq641 x y x
       have i₂ := eq198279 x
       grind)
    | exact superpose eq198279 eq641
    | exact resolve eq641 eq198279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198559 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq202937 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198472 (σ x)
       grind)
    | exact superpose eq198472 eq16
    | exact resolve eq16 eq198472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198472
  have eq211491 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq202937
       have i₂ := eq198279 x
       grind)
    | exact superpose eq198279 eq202937
    | exact resolve eq202937 eq198279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198279 eq202937
  have eq211524 : x = y ∨ x = (M.op x y) := by grind
  clear eq211491
  have eq211535 : x = (M.op x y) := by
    first
    | (have r₁ := eq211524
       have r₂ := eq198559
       grind)
    | exact resolve eq211524 eq198559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198559 eq211524
  have eq211610 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq641 x y x
       have i₂ := eq211535
       grind)
    | exact superpose eq211535 eq641
    | exact resolve eq641 eq211535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq211614 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq777 y x
       have i₂ := eq211535
       grind)
    | exact superpose eq211535 eq777
    | exact resolve eq777 eq211535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227408 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211614
       grind)
    | exact superpose eq211614 eq16
    | exact resolve eq16 eq211614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211614
  have eq227612 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq227408
       have i₂ := eq211535
       grind)
    | exact superpose eq211535 eq227408
    | exact resolve eq227408 eq211535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211535 eq227408
  have eq227613 : (σ x) = (σ y) := by grind
  clear eq227612
  have eq227653 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq227613
       grind)
    | exact superpose eq227613 eq16
    | exact resolve eq16 eq227613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227723 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ x)) ∨ (σ x) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq777 y x
       have i₂ := eq227613
       grind)
    | exact superpose eq227613 eq777
    | exact resolve eq777 eq227613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq227613
  have eq228021 : ∀ X0 : G, (σ x) = (σ (M.op X0 y)) ∨ (σ x) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq227723 X0
       have i₂ := eq211610 (σ (M.op X0 y))
       grind)
    | exact superpose eq211610 eq227723
    | (have j0 := eq227723 X0
       grind)
    | exact resolve eq227723 eq211610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227723
  have eq228022 : ∀ X0 : G, (σ x) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq228021 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228021
  have eq228059 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq227653
       have i₂ := eq211610 (σ x)
       grind)
    | exact superpose eq211610 eq227653
    | exact resolve eq227653 eq211610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211610 eq227653
  have eq228103 : False := by grind
  exact eq228103

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_y_pxx_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq21 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq23 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq47 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 x (M.op X0 X1)
       have i₂ := eq23 X0 X1 x
       grind)
    | exact superpose eq23 eq47
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq61 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | (have j0 := eq57 X0
       grind)
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq65 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq103 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X1 (σ X0)) X0
       have i₂ := eq47 X1 (σ X0)
       grind)
    | exact superpose eq47 eq61
    | exact resolve eq61 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq123 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq49
    | (have j0 := eq49 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ X1) (σ X0) x
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq23
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq23 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq172 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq123 X0 (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq123
    | (have j1 := eq35 X0
       grind)
    | exact resolve eq123 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq123
  have eq185 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq172
    | (have j0 := eq172 X0
       grind)
    | exact resolve eq172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq523 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq103 (M.op X0 X1)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq103
    | (have j0 := eq103 (M.op X0 X1)
       grind)
    | exact resolve eq103 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq103 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq103
    | (have j0 := eq103 (τ X0)
       grind)
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq528 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq529 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq527 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq527
    | (have j0 := eq527 X0
       grind)
    | exact resolve eq527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq532 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq529
    | (have j0 := eq529 X0
       grind)
    | exact resolve eq529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq539 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq532 (τ X0)
       have i₂ := eq110 X0 X0
       grind)
    | exact superpose eq110 eq532
    | (have j0 := eq532 (τ X0)
       grind)
    | exact resolve eq532 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq542 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq572 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq542 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq542
    | (have j0 := eq542 X0
       grind)
    | exact resolve eq542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq597 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (k X0 X0)
       have i₂ := eq572 X0
       grind)
    | exact superpose eq572 eq61
    | (have j1 := eq572 X0
       grind)
    | exact resolve eq61 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (k X0 X0) X1
       have i₂ := eq572 X0
       grind)
    | exact superpose eq572 eq71
    | (have j1 := eq572 X0
       grind)
    | exact resolve eq71 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq71 (M.op X0 X0) X1
       grind)
    | exact superpose eq71 eq602
    | (have j0 := eq602 X0 X1
       grind)
    | exact resolve eq602 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq602
  have eq611 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq61 X1 (M.op X0 X0)
       grind)
    | exact superpose eq61 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq597
  have eq677 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq720 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq742 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq528 X0 X1
       grind)
    | exact superpose eq528 eq23
    | exact resolve eq23 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq863 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq152 y x X0
       grind)
    | exact superpose eq152 eq16
    | (have j1 := eq152 y x X0
       grind)
    | exact resolve eq16 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq929 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (M.op X1 X0) = X0 ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq863 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq863
    | (have j0 := eq863 X0 X1 X2
       grind)
    | exact resolve eq863 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq863
  have eq1414 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq157 X1 X0
       grind)
    | exact superpose eq157 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq157 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq157 X0 X1
       grind)
    | exact resolve eq12 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1433 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1414 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq1414 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq1414 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1445 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1433
    | (have j0 := eq1433 X0 X1
       grind)
    | exact resolve eq1433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq1446 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1536 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (M.op X0 X1)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq539
    | (have j0 := eq539 (M.op X0 X1)
       grind)
    | exact resolve eq539 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1545 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1729 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq1545 X0 X1
       grind)
    | exact superpose eq1545 eq23
    | exact resolve eq23 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq2209 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq185 (τ X0)
       grind)
    | exact superpose eq185 eq19
    | (have j1 := eq185 (τ X0)
       grind)
    | exact resolve eq19 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2219 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2209 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2209
    | (have j0 := eq2209 X0
       grind)
    | exact resolve eq2209 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2238 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2219 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2219
    | (have j0 := eq2219 X0
       grind)
    | exact resolve eq2219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219
  have eq2248 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2238 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2238
    | (have j0 := eq2238 X0
       grind)
    | exact resolve eq2238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq3494 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq929 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq929
    | (have j0 := eq929 X1 X2 X2
       grind)
    | exact resolve eq929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq3723 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X0) = X0 ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq51 X2 x
       have i₂ := eq3494 X0 x X2
       grind)
    | exact superpose eq3494 eq51
    | (have j1 := eq3494 X2 X0 X2
       grind)
    | exact resolve eq51 eq3494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq3933 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1446 (τ X0) (τ X1)
       have i₂ := eq110 X1 X0
       grind)
    | exact superpose eq110 eq1446
    | (have j0 := eq1446 (τ X0) (τ X1)
       grind)
    | exact resolve eq1446 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1446
  have eq3968 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3933 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3933
    | (have j0 := eq3933 X0 X1
       grind)
    | exact resolve eq3933 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933
  have eq3977 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3968 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3968
    | (have j0 := eq3968 X0 X1
       grind)
    | exact resolve eq3968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq3983 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3977 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq3977
    | (have j0 := eq3977 X0 X1
       grind)
    | exact resolve eq3977 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3977
  have eq3987 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3983 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3983
    | (have j0 := eq3983 X0 X1
       grind)
    | exact resolve eq3983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq3991 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3987 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3987
    | (have j0 := eq3987 X0 X1
       grind)
    | exact resolve eq3987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987
  have eq3992 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3991 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3991
    | (have j0 := eq3991 X0 X1
       grind)
    | exact resolve eq3991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq3993 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3992 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3992
    | (have j0 := eq3992 X0 X1
       grind)
    | exact resolve eq3992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4557 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3993 (k X0 X0) X0
       have i₂ := eq2248 X0
       grind)
    | exact superpose eq2248 eq3993
    | (have j0 := eq3993 (k X0 X0) X0
       have j1 := eq2248 X0
       grind)
    | (have r₁ := eq3993 (k X0 X0) X0
       have r₂ := eq2248 X0
       grind)
    | exact resolve eq3993 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248 eq3993
  have eq4560 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4580 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4560 X0
       have j1 := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq4560 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq4560 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560
  have eq10522 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4580 X0
       have i₂ := eq3723 X0 (k X0 X0)
       grind)
    | exact superpose eq3723 eq4580
    | (have j0 := eq4580 X0
       have j1 := eq3723 X0 (k X0 X0)
       grind)
    | exact resolve eq4580 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723 eq4580
  have eq10659 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10522 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10522
  have eq10863 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 (k X0 X0) X0
       have i₂ := eq10659 X0
       grind)
    | exact superpose eq10659 eq51
    | (have j1 := eq10659 (k X0 X0)
       grind)
    | exact resolve eq51 eq10659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10659
  have eq13358 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq875 X0
       have i₂ := eq720 x y
       grind)
    | exact superpose eq720 eq875
    | (have j0 := eq875 X0
       have j1 := eq720 x y
       grind)
    | (have r₁ := eq875 X0
       have r₂ := eq720 x y
       grind)
    | (have r₁ := eq875 X0
       have r₂ := eq720 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq875 X0
       have r₂ := eq720 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq875 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq875
  have eq13359 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq13358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13358
  have eq108856 : ∀ X0 X1 : G, (k (k X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq606
    | (have j0 := eq606 X1 X1
       grind)
    | exact resolve eq606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq110328 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10863 X0
       have i₂ := eq108856 (k X0 X0) X0
       grind)
    | exact superpose eq108856 eq10863
    | (have j0 := eq10863 X0
       have j1 := eq108856 X0 X0
       grind)
    | exact resolve eq10863 eq108856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10863 eq108856
  have eq110645 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq110328 X0
       have j1 := eq12 (M.op X0 X0) (k X0 X0)
       grind)
    | (have r₁ := eq110328 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq110328 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110328
  have eq113881 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq611
    | (have j0 := eq611 X1 X1
       grind)
    | exact resolve eq611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq114452 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq110645 X0
       have i₂ := eq113881 (M.op X0 X0) X0
       grind)
    | exact superpose eq113881 eq110645
    | (have j0 := eq110645 X0
       have j1 := eq113881 X0 X0
       grind)
    | exact resolve eq110645 eq113881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110645 eq113881
  have eq114546 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq114452 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq114452 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq114452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114452
  have eq114583 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq114546 X0
       have i₂ := eq51 X0 X0
       grind)
    | exact superpose eq51 eq114546
    | (have j0 := eq114546 X0
       grind)
    | exact resolve eq114546 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq114546
  have eq114959 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114583 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq114583
    | exact resolve eq114583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114583
  have eq236596 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq1729 x (σ y) x
       have i₂ := eq13359 x
       grind)
    | exact superpose eq13359 eq1729
    | exact resolve eq1729 eq13359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq13359
  have eq236606 : ∀ X1 : G, y = (M.op y x) ∨ y = (M.op X1 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq236596 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq236596
    | exact resolve eq236596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236596
  have eq238066 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 y x x
       have i₂ := eq236606 X1
       grind)
    | exact superpose eq236606 eq23
    | (have j1 := eq236606 X1
       grind)
    | exact resolve eq23 eq236606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236606
  have eq238547 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq238066 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238066
  have eq238548 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq238547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238547
  have eq238648 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq742 x y x
       have i₂ := eq238548 x
       grind)
    | exact superpose eq238548 eq742
    | exact resolve eq742 eq238548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239112 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq238648 (σ x)
       grind)
    | exact superpose eq238648 eq16
    | exact resolve eq16 eq238648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238648
  have eq239785 : (σ y) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq239112
       have i₂ := eq238548 x
       grind)
    | exact superpose eq238548 eq239112
    | exact resolve eq239112 eq238548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238548 eq239112
  have eq239808 : (σ y) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq239785
  have eq239809 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq239808
  have eq239879 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq239809
       grind)
    | exact superpose eq239809 eq10
    | exact resolve eq10 eq239809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239809
  have eq240028 : x = y ∨ x = y := by
    first
    | (have i₁ := eq239879
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq239879
    | exact resolve eq239879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239879
  have eq240029 : x = y := by grind
  clear eq240028
  have eq240049 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq240029
       grind)
    | exact superpose eq240029 eq16
    | exact resolve eq16 eq240029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240029
  have eq240293 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq240049
       have i₂ := eq114959 x
       grind)
    | exact superpose eq114959 eq240049
    | (have j1 := eq114959 x
       grind)
    | exact resolve eq240049 eq114959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114959
  have eq244999 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq240293
       have i₂ := eq572 x
       grind)
    | exact superpose eq572 eq240293
    | (have j1 := eq572 x
       grind)
    | (have r₁ := eq240293
       have r₂ := eq572 x
       grind)
    | exact resolve eq240293 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq240293
  have eq245000 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq244999
  have eq245032 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq245000
       grind)
    | exact superpose eq245000 eq10
    | exact resolve eq10 eq245000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245000
  have eq245107 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq245032
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq245032
    | exact resolve eq245032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245032
  have eq245108 : x = (M.op x x) := by grind
  clear eq245107
  have eq245137 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq23 x x x
       have i₂ := eq245108
       grind)
    | exact superpose eq245108 eq23
    | exact resolve eq23 eq245108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq245145 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq742 x x x
       have i₂ := eq245108
       grind)
    | exact superpose eq245108 eq742
    | exact resolve eq742 eq245108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq245108
  have eq245696 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq240049
       have i₂ := eq245145 (σ x)
       grind)
    | exact superpose eq245145 eq240049
    | exact resolve eq240049 eq245145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240049 eq245145
  have eq245742 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq245696
       have i₂ := eq245137 x
       grind)
    | exact superpose eq245137 eq245696
    | exact resolve eq245696 eq245137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245137 eq245696
  have eq245743 : False := by grind
  exact eq245743

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pxx_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq22 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X1 (M.op X0 X1)
       have r₂ := eq27 X0 X1
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 x (M.op X0 X1)
       have i₂ := eq22 X0 X1 x
       grind)
    | exact superpose eq22 eq47
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq136 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (M.op X1 (σ X0))
       have i₂ := eq47 X1 (σ X0)
       grind)
    | exact superpose eq47 eq89
    | exact resolve eq89 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq89
  have eq148 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq319 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X1) (σ X0) x
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq22
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq22 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq50 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq324 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq753 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (M.op X0 X1)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq324
    | (have j0 := eq324 (M.op X0 X1)
       grind)
    | exact resolve eq324 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq757 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq324 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq324
    | (have j0 := eq324 (τ X0)
       grind)
    | exact resolve eq324 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq758 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq753 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq761 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq757 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq757
    | (have j0 := eq757 X0
       grind)
    | exact resolve eq757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq764 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq761 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq761
    | (have j0 := eq761 X0
       grind)
    | exact resolve eq761 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq1125 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq758 X0 X1
       grind)
    | exact superpose eq758 eq22
    | exact resolve eq22 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq3278 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq319 X0 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq3279 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3278
  have eq18515 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3279 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3279
    | exact resolve eq3279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18555 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ X0)
       have i₂ := eq3279 X0 X1
       grind)
    | exact superpose eq3279 eq148
    | (have j1 := eq3279 X0 X1
       grind)
    | exact resolve eq148 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq3279
  have eq18805 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18555 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18555
    | (have j0 := eq18555 X0 X1
       grind)
    | exact resolve eq18555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18555
  have eq18807 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18515 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq18515
    | (have j0 := eq18515 X0 X1
       grind)
    | exact resolve eq18515 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18515
  have eq20363 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18807 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18807
    | (have j0 := eq18807 X1 X1
       grind)
    | exact resolve eq18807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807
  have eq21203 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 X1 x
       have i₂ := eq20363 X0 X1
       grind)
    | exact superpose eq20363 eq22
    | (have j1 := eq20363 X2 X0
       grind)
    | exact resolve eq22 eq20363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20363
  have eq42550 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18805 y x
       grind)
    | exact superpose eq18805 eq16
    | (have j1 := eq18805 y x
       grind)
    | exact resolve eq16 eq18805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805
  have eq44279 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq42550
       have i₂ := eq21203 y X0 x
       grind)
    | exact superpose eq21203 eq42550
    | (have j1 := eq21203 y X0 x
       grind)
    | exact resolve eq42550 eq21203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21203 eq42550
  have eq44287 : ∀ X0 : G, y = (k y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq44279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44279
  have eq44996 : y = (M.op y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq27 x y
       have i₂ := eq44287 x
       grind)
    | exact superpose eq44287 eq27
    | (have j1 := eq44287 y
       grind)
    | exact resolve eq27 eq44287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq44287
  have eq45118 : y = (M.op y y) := by
    first
    | (have j1 := eq764 y
       grind)
    | (have r₁ := eq44996
       have r₂ := eq764 y
       grind)
    | exact resolve eq44996 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq44996
  have eq45875 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22 y y x
       have i₂ := eq45118
       grind)
    | exact superpose eq45118 eq22
    | exact resolve eq22 eq45118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq45894 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1125 y y x
       have i₂ := eq45118
       grind)
    | exact superpose eq45118 eq1125
    | exact resolve eq1125 eq45118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq45118
  have eq47856 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45894 (σ x)
       grind)
    | exact superpose eq45894 eq16
    | exact resolve eq16 eq45894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45894
  have eq47887 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq47856
       have i₂ := eq45875 x
       grind)
    | exact superpose eq45875 eq47856
    | exact resolve eq47856 eq45875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45875 eq47856
  have eq47888 : False := by grind
  exact eq47888

/-- `Equation3588`: `x ◇ y = z ◇ ((x ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3588 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3588 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3588.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq81 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq86 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq425 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq459 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq81
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq81
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq831 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq830
  have eq4891 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq16
    | exact resolve eq16 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4893 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq831
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq831
       grind)
    | exact resolve eq13 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq4909 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4893
  have eq4910 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4909
  have eq4912 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4910
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4910
    | exact resolve eq4910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4910
  have eq8144 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq4912
       grind)
    | exact superpose eq4912 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq8149 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq4912
       grind)
    | exact superpose eq4912 eq10
    | exact resolve eq10 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq8189 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8144
  have eq8216 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8149
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8149
    | exact resolve eq8149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8149
  have eq8217 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8189
       have r₂ := eq4891
       grind)
    | exact resolve eq8189 eq4891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891 eq8189
  have eq8220 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq8216
       have r₂ := eq13 y x
       grind)
    | exact resolve eq8216 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8216
  have eq8616 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq86 x y
       have i₂ := eq8220
       grind)
    | exact superpose eq8220 eq86
    | (have j0 := eq86 x y
       grind)
    | exact resolve eq86 eq8220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq8220
  have eq8628 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8616
  have eq8629 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8628
  have eq9247 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8629
       grind)
    | exact superpose eq8629 eq16
    | exact resolve eq16 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq9429 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9247
       have i₂ := eq8217
       grind)
    | exact superpose eq8217 eq9247
    | exact resolve eq9247 eq8217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8217 eq9247
  have eq9430 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9429
  have eq9431 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq9430
  have eq9590 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9431
       grind)
    | exact superpose eq9431 eq10
    | exact resolve eq10 eq9431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9431
  have eq9657 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9590
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9590
    | exact resolve eq9590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9590
  have eq9658 : x = y := by grind
  clear eq9657
  have eq9858 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9658
       grind)
    | exact superpose eq9658 eq16
    | exact resolve eq16 eq9658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9658
  have eq9859 : False := by grind
  exact eq9859

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3735 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3735 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X1 X0) = (k (M.op X0 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X2) (M.op X1 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X1 X0)
       have r₂ := eq9 X0 X1 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 X2) (M.op X1 X0)
       grind)
    | (have r₁ := eq13 (M.op X0 X2) (M.op X0 X0)
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq25
    | exact resolve eq25 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq62 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq32
    | exact resolve eq32 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq169 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq59 X0 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1 X2 X1
       have i₂ := eq59 X1 X0 (M.op X0 X2)
       grind)
    | exact superpose eq59 eq19
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq187 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = (k (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq59 X1 X0 X2
       grind)
    | exact superpose eq59 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have r₁ := eq12 (M.op X1 X0) (M.op X0 X2)
       have r₂ := eq59 X0 X1 X2
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq187 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq208 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq169 X0 X1 X2 X3
       have i₂ := eq180 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq180 eq169
    | exact resolve eq169 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq214 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq208 X0 X1 x X3
       have i₂ := eq180 X1 X3 x
       grind)
    | exact superpose eq180 eq208
    | exact resolve eq208 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq227 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq308 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X0 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) X1
       have i₂ := eq180 X0 X1 X2
       grind)
    | exact superpose eq180 eq12
    | (have j0 := eq12 (M.op X0 X2) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq180 X0 X1 X1
       grind)
    | exact resolve eq12 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (σ X1) (σ X0) X2
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq59
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq59 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq372 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1 x
       have i₂ := eq214 (σ (k X0 X1)) (σ X1) x
       grind)
    | exact superpose eq214 eq370
    | (have j0 := eq370 X0 X1 x
       grind)
    | exact resolve eq370 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq407 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X2) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 X2)
       have i₂ := eq214 X0 X1 X2
       grind)
    | exact superpose eq214 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 x)
       have i₂ := eq214 X0 X1 x
       grind)
    | exact superpose eq214 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq214 X0 X0 X0
       grind)
    | exact resolve eq13 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (M.op (σ X1) (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 (σ X0) (σ X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq158
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq158 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1079 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq1143 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (τ X0))
       have i₂ := eq1079 X1 (τ X0)
       grind)
    | exact superpose eq1079 eq18
    | exact resolve eq18 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X1 (σ X0)) X0
       have i₂ := eq1079 X1 (σ X0)
       grind)
    | exact superpose eq1079 eq25
    | exact resolve eq25 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1146
    | exact resolve eq1146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1151 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1143 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1143
    | exact resolve eq1143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1182 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = (k (τ (M.op X2 (k (σ X0) X1))) (k X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1149 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq1149
    | exact resolve eq1149 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 (σ (σ X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (τ (M.op X1 (σ (σ X0)))) X0
       have i₂ := eq1149 (σ X0) X1
       grind)
    | exact superpose eq1149 eq25
    | exact resolve eq25 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1196 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 (σ (σ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1193
    | exact resolve eq1193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1241 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 (τ (τ X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (M.op X1 (τ (τ X0))))
       have i₂ := eq1151 (τ X0) X1
       grind)
    | exact superpose eq1151 eq18
    | exact resolve eq18 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1251 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 (τ (τ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1241 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1241
    | exact resolve eq1241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq2597 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k (M.op (σ X0) X1) (σ (k X0 X0))) ∨ (M.op (σ X0) X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 (σ X1) X1
       have i₂ := eq36 X1 X1
       grind)
    | exact superpose eq36 eq227
    | (have j1 := eq36 X0 X0
       grind)
    | exact resolve eq227 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq227
  have eq2609 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k (M.op (σ X0) X1) (σ (k X0 X0))) ∨ (M.op (σ X0) X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq8978 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X2 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op X2 X0)) = (M.op (σ (M.op X2 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq372 (M.op X2 X0) (M.op X0 X1)
       have i₂ := eq195 X2 X0 X1
       grind)
    | exact superpose eq195 eq372
    | (have j0 := eq372 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact resolve eq372 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8989 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq372 (τ X0) (τ X1)
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq372
    | (have j0 := eq372 (τ X0) (τ X1)
       grind)
    | exact resolve eq372 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq9014 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X2 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op X2 X0)) = (M.op (σ (M.op X2 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8978 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8978
  have eq9025 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8989 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq8989
    | (have j0 := eq8989 X0 X1
       grind)
    | exact resolve eq8989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8989
  have eq9035 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9025 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9025
    | (have j0 := eq9025 X0 X1
       grind)
    | exact resolve eq9025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9025
  have eq9040 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9035 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9035
    | (have j0 := eq9035 X0 X1
       grind)
    | exact resolve eq9035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9035
  have eq9043 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9040 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9040
    | (have j0 := eq9040 X0 X1
       grind)
    | exact resolve eq9040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9040
  have eq9046 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9043 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9043
    | (have j0 := eq9043 X0 X1
       grind)
    | exact resolve eq9043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9043
  have eq9047 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9046 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9046
    | (have j0 := eq9046 X0 X1
       grind)
    | exact resolve eq9046 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9046
  have eq12469 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq408 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq13469 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq12469 (τ X0)
       grind)
    | exact superpose eq12469 eq17
    | (have j1 := eq12469 (τ X0)
       grind)
    | exact resolve eq17 eq12469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12469
  have eq13479 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq13469 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13469
    | (have j0 := eq13469 X0
       grind)
    | exact resolve eq13469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13469
  have eq15549 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq13479 X0
       have i₂ := eq38 (τ X0) X0
       grind)
    | exact superpose eq38 eq13479
    | (have j0 := eq13479 X0
       have j1 := eq38 (τ X0) X0
       grind)
    | exact resolve eq13479 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq13479
  have eq15586 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq15549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15549
  have eq15605 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15586 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15586
    | (have j0 := eq15586 X0
       grind)
    | exact resolve eq15586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15586
  have eq17199 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq15605 (τ X0)
       grind)
    | exact superpose eq15605 eq17
    | (have j1 := eq15605 (τ X0)
       grind)
    | exact resolve eq17 eq15605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq15605
  have eq17209 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17199 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17199
    | (have j0 := eq17199 X0
       grind)
    | exact resolve eq17199 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq17228 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17209 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17209
    | (have j0 := eq17209 X0
       grind)
    | exact resolve eq17209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17209
  have eq22371 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1251 X0 (τ (τ X0))
       have i₂ := eq17228 X0
       grind)
    | exact superpose eq17228 eq1251
    | (have j1 := eq17228 X0
       grind)
    | exact resolve eq1251 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq22443 : ∀ X0 : G, (τ (τ X0)) = (k (τ (τ X0)) (τ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1079 (τ (τ X0)) (τ (τ X0))
       have i₂ := eq17228 X0
       grind)
    | exact superpose eq17228 eq1079
    | (have j1 := eq17228 X0
       grind)
    | exact resolve eq1079 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17228
  have eq22457 : ∀ X0 : G, (τ (τ X0)) = (τ (k (τ X0) (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22443 X0
       have i₂ := eq39 (τ X0) (τ X0)
       grind)
    | exact superpose eq39 eq22443
    | (have j0 := eq22443 X0
       grind)
    | exact resolve eq22443 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22443
  have eq22485 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22371 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq22371
    | (have j0 := eq22371 X0
       grind)
    | exact resolve eq22371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22371
  have eq22522 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22457 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq22457
    | (have j0 := eq22457 X0
       grind)
    | exact resolve eq22457 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22457
  have eq22537 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22485 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22485
    | (have j0 := eq22485 X0
       grind)
    | exact resolve eq22485 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22485
  have eq25331 : ∀ X0 X1 : G, (k (τ X1) (τ (τ X0))) = (τ (k X1 (τ (k X0 X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (τ (k X0 X0)) X1
       have i₂ := eq22522 X0
       grind)
    | exact superpose eq22522 eq39
    | (have j1 := eq22522 X0
       grind)
    | exact resolve eq39 eq22522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22522
  have eq25487 : ∀ X0 X1 : G, (τ (k X1 (τ (k X0 X0)))) = (τ (k X1 (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25331 X0 X1
       have i₂ := eq39 (τ X0) X1
       grind)
    | exact superpose eq39 eq25331
    | (have j0 := eq25331 X0 X1
       grind)
    | exact resolve eq25331 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25331
  have eq27248 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (τ X1) (τ X0)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq374
    | (have j0 := eq374 (τ X0) (τ X1)
       grind)
    | exact resolve eq374 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq27478 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27248 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27248
    | (have j0 := eq27248 X0 X1
       grind)
    | exact resolve eq27248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248
  have eq27520 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27478 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27478
    | (have j0 := eq27478 X0 X1
       grind)
    | exact resolve eq27478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27478
  have eq27549 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27520 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27520
    | (have j0 := eq27520 X0 X1
       grind)
    | exact resolve eq27520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27520
  have eq27568 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27549 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27549
    | (have j0 := eq27549 X0 X1
       grind)
    | exact resolve eq27549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27549
  have eq27580 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27568 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27568
    | (have j0 := eq27568 X0 X1
       grind)
    | exact resolve eq27568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27568
  have eq27587 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27580 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27580
    | (have j0 := eq27580 X0 X1
       grind)
    | exact resolve eq27580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27580
  have eq32998 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq463 X0 X0
       have i₂ := eq2609 X0 (σ X0)
       grind)
    | exact superpose eq2609 eq463
    | (have j0 := eq463 X0 X0
       have j1 := eq2609 X0 (σ X0)
       grind)
    | exact resolve eq463 eq2609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq2609
  have eq33025 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32998
  have eq33184 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33025 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33025
    | exact resolve eq33025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33233 : ∀ X0 : G, (k (τ (τ (σ (k (σ X0) (σ X0))))) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1196 X0 (σ (σ X0))
       have i₂ := eq33025 (σ X0)
       grind)
    | exact superpose eq33025 eq1196
    | (have j1 := eq33025 (σ X0)
       grind)
    | exact resolve eq1196 eq33025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33323 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33025
  have eq33399 : ∀ X0 : G, (k (τ (k (σ X0) (σ X0))) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33233 X0
       have i₂ := eq10 (k (σ X0) (σ X0))
       grind)
    | exact superpose eq10 eq33233
    | (have j0 := eq33233 X0
       grind)
    | exact resolve eq33233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33233
  have eq33416 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33184 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq33184
    | (have j0 := eq33184 X0
       grind)
    | exact resolve eq33184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33184
  have eq33464 : ∀ X0 : G, (k (k (τ (σ X0)) X0) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33399 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq33399
    | (have j0 := eq33399 X0
       grind)
    | exact resolve eq33399 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33399
  have eq33477 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33416 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33416
    | (have j0 := eq33416 X0
       grind)
    | exact resolve eq33416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33416
  have eq33497 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33464 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33464
    | (have j0 := eq33464 X0
       grind)
    | exact resolve eq33464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33464
  have eq33868 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq33477 (σ X0)
       grind)
    | exact superpose eq33477 eq32
    | (have j1 := eq33477 (σ X0)
       grind)
    | exact resolve eq32 eq33477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq33477
  have eq33964 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq33868 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33868
    | (have j0 := eq33868 X0
       grind)
    | exact resolve eq33868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33868
  have eq34312 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33323 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq33323
    | (have j0 := eq33323 (τ X0)
       grind)
    | exact resolve eq33323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33323
  have eq34357 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34312 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34312
    | (have j0 := eq34312 X0
       grind)
    | exact resolve eq34312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34312
  have eq34376 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34357 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34357
    | (have j0 := eq34357 X0
       grind)
    | exact resolve eq34357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34357
  have eq34833 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34376 (τ X0)
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq34376
    | (have j0 := eq34376 (τ X0)
       grind)
    | exact resolve eq34376 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37305 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34833 (M.op X0 X0)
       have i₂ := eq195 X0 X0 X0
       grind)
    | exact superpose eq195 eq34833
    | (have j0 := eq34833 (M.op X0 X0)
       grind)
    | exact resolve eq34833 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34833
  have eq37316 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq37305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37305
  have eq43278 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33964 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33964
    | exact resolve eq33964 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33964
  have eq43456 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43278 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq43278
    | (have j0 := eq43278 X0
       grind)
    | exact resolve eq43278 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43278
  have eq43732 : ∀ X0 X1 : G, (k (τ X1) (τ (M.op X0 X0))) = (τ (k X1 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k X0 X0) X1
       have i₂ := eq43456 X0
       grind)
    | exact superpose eq43456 eq39
    | (have j1 := eq43456 X0
       grind)
    | exact resolve eq39 eq43456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43456
  have eq43845 : ∀ X0 X1 : G, (τ (k X1 (k X0 X0))) = (τ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43732 X0 X1
       have i₂ := eq39 (M.op X0 X0) X1
       grind)
    | exact superpose eq39 eq43732
    | (have j0 := eq43732 X0 X1
       grind)
    | exact resolve eq43732 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43732
  have eq48496 : ∀ X0 : G, (k (τ (τ (σ (σ X0)))) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1196 X0 (σ (σ X0))
       have i₂ := eq33497 X0
       grind)
    | exact superpose eq33497 eq1196
    | (have j1 := eq33497 X0
       grind)
    | exact resolve eq1196 eq33497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq33497
  have eq48630 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48496 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq48496
    | (have j0 := eq48496 X0
       grind)
    | exact resolve eq48496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48496
  have eq48714 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48630 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48630
    | (have j0 := eq48630 X0
       grind)
    | exact resolve eq48630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48630
  have eq49028 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq48714 (τ X0)
       grind)
    | exact superpose eq48714 eq18
    | (have j1 := eq48714 (τ X0)
       grind)
    | exact resolve eq18 eq48714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49116 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49028 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq49028
    | (have j0 := eq49028 X0
       grind)
    | exact resolve eq49028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49028
  have eq49173 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49116 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49116
    | (have j0 := eq49116 X0
       grind)
    | exact resolve eq49116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49116
  have eq49222 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49173 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq49173
    | (have j0 := eq49173 X0
       grind)
    | exact resolve eq49173 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49173
  have eq50784 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq49222 (τ X0)
       grind)
    | exact superpose eq49222 eq18
    | (have j1 := eq49222 (τ X0)
       grind)
    | exact resolve eq18 eq49222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49222
  have eq50867 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50784 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq50784
    | (have j0 := eq50784 X0
       grind)
    | exact resolve eq50784 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50784
  have eq50923 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50867 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50867
    | (have j0 := eq50867 X0
       grind)
    | exact resolve eq50867 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50867
  have eq50975 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50923 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq50923
    | (have j0 := eq50923 X0
       grind)
    | exact resolve eq50923 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50923
  have eq55301 : ∀ X0 X1 : G, (k (τ (τ X0)) (τ X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (k X0 X0))
       have i₂ := eq50975 X0
       grind)
    | exact superpose eq50975 eq39
    | (have j1 := eq50975 X0
       grind)
    | exact resolve eq39 eq50975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50975
  have eq55586 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55301 X0 X1
       have i₂ := eq39 X1 (τ X0)
       grind)
    | exact superpose eq39 eq55301
    | (have j0 := eq55301 X0 X1
       grind)
    | exact resolve eq55301 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55301
  have eq69985 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k (M.op X1 (k X0 X0)) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43845 X0 (M.op X1 (k X0 X0))
       have i₂ := eq1079 X1 (k X0 X0)
       grind)
    | exact superpose eq1079 eq43845
    | (have j0 := eq43845 X0 X1
       grind)
    | exact resolve eq43845 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43845
  have eq164514 : ∀ X0 X1 : G, (k X0 (τ (k X1 X1))) = (σ (τ (k X0 (τ X1)))) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (τ (k X1 X1)))
       have i₂ := eq25487 X1 X0
       grind)
    | exact superpose eq25487 eq11
    | (have j1 := eq25487 X1 X1
       grind)
    | exact resolve eq11 eq25487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25487
  have eq164550 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k X0 (τ (k X1 X1))) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164514 X0 X1
       have i₂ := eq11 (k X0 (τ X1))
       grind)
    | exact superpose eq11 eq164514
    | (have j0 := eq164514 X0 X1
       grind)
    | exact resolve eq164514 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164514
  have eq164806 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (k X1 (τ (σ X0))) = (k X1 (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 (σ X0) (σ X0)
       have i₂ := eq164550 X1 (σ X0)
       grind)
    | exact superpose eq164550 eq41
    | (have j1 := eq164550 X1 (σ X0)
       grind)
    | exact resolve eq41 eq164550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq164550
  have eq164837 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X1 (τ (σ X0))) = (k X1 (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164806 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164806
    | (have j0 := eq164806 X0 X1
       grind)
    | exact resolve eq164806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164806
  have eq164928 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (k X1 (k (τ (σ X0)) X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164837 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq164837
    | (have j0 := eq164837 X0 X1
       grind)
    | exact resolve eq164837 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164837
  have eq164979 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164928 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164928
    | (have j0 := eq164928 X0 X1
       grind)
    | exact resolve eq164928 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164928
  have eq165362 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq164979 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164979
  have eq165377 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq165362 X0
       have j1 := eq22537 X0
       grind)
    | (have r₁ := eq165362 X0
       have r₂ := eq22537 X0
       grind)
    | exact resolve eq165362 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22537 eq165362
  have eq165646 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq27587 X0 (k X0 X0)
       have i₂ := eq165377 X0
       grind)
    | exact superpose eq165377 eq27587
    | (have j0 := eq27587 X0 (k X0 X0)
       grind)
    | exact resolve eq27587 eq165377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27587
  have eq165771 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq165646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165646
  have eq166203 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1 (k X0 X0)
       have i₂ := eq165771 X0
       grind)
    | exact superpose eq165771 eq180
    | (have j1 := eq165771 X0
       grind)
    | exact resolve eq180 eq165771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166208 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq214 X1 X0 (k X0 X0)
       have i₂ := eq165771 X0
       grind)
    | exact superpose eq165771 eq214
    | (have j1 := eq165771 X0
       grind)
    | exact resolve eq214 eq165771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166230 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq165771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166593 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X1) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1079 X0 (k X0 X0)
       have i₂ := eq166203 X0 X1
       grind)
    | exact superpose eq166203 eq1079
    | (have j1 := eq166203 X0 X1
       grind)
    | exact resolve eq1079 eq166203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166203
  have eq166630 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq166593 X0 X1
       have i₂ := eq165377 X0
       grind)
    | exact superpose eq165377 eq166593
    | (have j0 := eq166593 X0 X1
       grind)
    | exact resolve eq166593 eq165377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166593
  have eq166870 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X2 (k X0 X0) X1
       have i₂ := eq166630 X0 X1
       grind)
    | exact superpose eq166630 eq214
    | (have j1 := eq166630 X0 X1
       grind)
    | exact resolve eq214 eq166630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166954 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq166870 X0 x X2
       have i₂ := eq214 X2 X0 x
       grind)
    | exact superpose eq214 eq166870
    | (have j0 := eq166870 X0 x X2
       grind)
    | exact resolve eq166870 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166870
  have eq167100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq166954 X0 X0
       have i₂ := eq165771 X0
       grind)
    | exact superpose eq165771 eq166954
    | (have j0 := eq166954 X0 x
       have j1 := eq165771 X0
       grind)
    | exact resolve eq166954 eq165771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165771
  have eq167264 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq167100 X0
       have j1 := eq166230 X0
       grind)
    | (have r₁ := eq167100 X0
       have r₂ := eq166230 X0
       grind)
    | exact resolve eq167100 eq166230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166230 eq167100
  have eq167326 : ∀ X0 : G, (k X0 (τ (σ X0))) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1182 X0 (σ X0) (σ X0)
       have i₂ := eq167264 (σ X0)
       grind)
    | exact superpose eq167264 eq1182
    | (have j1 := eq167264 (σ X0)
       grind)
    | exact resolve eq1182 eq167264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq167383 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1079 X0 (k X0 X0)
       have i₂ := eq167264 X0
       grind)
    | exact superpose eq167264 eq1079
    | (have j1 := eq167264 X0
       grind)
    | exact resolve eq1079 eq167264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167264
  have eq167421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq167383 X0
       have i₂ := eq165377 X0
       grind)
    | exact superpose eq165377 eq167383
    | (have j0 := eq167383 X0
       grind)
    | exact resolve eq167383 eq165377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167383
  have eq167439 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq167326 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq167326
    | (have j0 := eq167326 X0
       grind)
    | exact resolve eq167326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167326
  have eq167452 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq167439 X0
       have i₂ := eq165377 X0
       grind)
    | exact superpose eq165377 eq167439
    | (have j0 := eq167439 X0
       grind)
    | exact resolve eq167439 eq165377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167439
  have eq167457 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq167452 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq167452
    | (have j0 := eq167452 X0
       grind)
    | exact resolve eq167452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167452
  have eq168173 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq167457 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq167457
    | (have j0 := eq167457 (τ X0)
       grind)
    | exact resolve eq167457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168222 : ∀ X0 : G, (τ (σ (k X0 X0))) = (M.op (τ (σ (k X0 X0))) (τ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37316 (σ X0)
       have i₂ := eq167457 X0
       grind)
    | exact superpose eq167457 eq37316
    | (have j1 := eq167457 X0
       grind)
    | exact resolve eq37316 eq167457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37316 eq167457
  have eq168340 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq168222 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq168222
    | (have j0 := eq168222 X0
       grind)
    | exact resolve eq168222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168222
  have eq168373 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq168173 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq168173
    | (have j0 := eq168173 X0
       grind)
    | exact resolve eq168173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq168173
  have eq168410 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq168373 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq168373
    | (have j0 := eq168373 X0
       grind)
    | exact resolve eq168373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168373
  have eq168430 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq168410 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq168410
    | (have j0 := eq168410 X0
       grind)
    | exact resolve eq168410 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168410
  have eq168464 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k (k X0 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (k X0 X0)
       have i₂ := eq168430 X0
       grind)
    | exact superpose eq168430 eq39
    | (have j1 := eq168430 X0
       grind)
    | exact resolve eq39 eq168430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168430
  have eq168593 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (k X0 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq168464 X0 X1
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq168464
    | (have j0 := eq168464 X0 X1
       grind)
    | exact resolve eq168464 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168464
  have eq169674 : ∀ X0 X1 : G, (τ (k X1 X1)) = (τ (k (M.op X0 X1) (M.op X1 X1))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69985 X1 X0
       have i₂ := eq166208 X1 X0
       grind)
    | exact superpose eq166208 eq69985
    | (have j0 := eq69985 X1 X1
       have j1 := eq166208 X1 X1
       grind)
    | exact resolve eq69985 eq166208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69985
  have eq169848 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq166208 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166208
  have eq169889 : ∀ X0 X1 : G, (τ (k X1 X1)) = (τ (k (M.op X0 X1) (M.op X1 X1))) ∨ (M.op X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq169674 X0 X1
       have j1 := eq169848 X1
       grind)
    | (have r₁ := eq169674 X0 X0
       have r₂ := eq169848 X0
       grind)
    | exact resolve eq169674 eq169848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169674
  have eq169911 : ∀ X1 : G, (M.op X1 (k X1 X1)) = X1 ∨ (τ (k X1 X1)) = (τ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq169889 x X1
       have i₂ := eq195 x X1 X1
       grind)
    | exact superpose eq195 eq169889
    | (have j0 := eq169889 x X1
       grind)
    | exact resolve eq169889 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq169889
  have eq169927 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169848 (M.op X0 X1)
       have i₂ := eq180 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq180 eq169848
    | (have j0 := eq169848 (M.op X0 X1)
       grind)
    | exact resolve eq169848 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169848
  have eq169969 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169927 X0 X1
       have i₂ := eq214 X0 X0 X1
       grind)
    | exact superpose eq214 eq169927
    | (have j0 := eq169927 X0 X1
       grind)
    | (have r₁ := eq169927 x x
       have r₂ := eq214 x x x
       grind)
    | exact resolve eq169927 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169927
  have eq169981 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169969 X0 X1
       have i₂ := eq180 X0 (k (M.op X0 X1) (M.op X0 X1)) X1
       grind)
    | exact superpose eq180 eq169969
    | (have j0 := eq169969 X0 X1
       grind)
    | exact resolve eq169969 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169969
  have eq170478 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1079 X0 (k X0 X0)
       have i₂ := eq169911 X0
       grind)
    | exact superpose eq169911 eq1079
    | (have j1 := eq169911 X0
       grind)
    | exact resolve eq1079 eq169911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq169911
  have eq170503 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq170478 X0
       have i₂ := eq165377 X0
       grind)
    | exact superpose eq165377 eq170478
    | (have j0 := eq170478 X0
       grind)
    | exact resolve eq170478 eq165377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170478
  have eq170559 : ∀ X0 X1 : G, (k (τ X1) (τ (M.op X0 X0))) = (τ (k X1 (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k X0 X0) X1
       have i₂ := eq170503 X0
       grind)
    | exact superpose eq170503 eq39
    | (have j1 := eq170503 X0
       grind)
    | exact resolve eq39 eq170503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170503
  have eq170679 : ∀ X0 X1 : G, (τ (k X1 (k X0 X0))) = (τ (k X1 (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq170559 X0 X1
       have i₂ := eq39 (M.op X0 X0) X1
       grind)
    | exact superpose eq39 eq170559
    | (have j0 := eq170559 X0 X1
       grind)
    | exact resolve eq170559 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170559
  have eq172584 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq166630 X0 (k X0 X0)
       have i₂ := eq168340 X0
       grind)
    | exact superpose eq168340 eq166630
    | (have j0 := eq166630 X0 x
       have j1 := eq168340 X0
       grind)
    | exact resolve eq166630 eq168340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166630
  have eq172594 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq166954 X0 (k X0 X0)
       have i₂ := eq168340 X0
       grind)
    | exact superpose eq168340 eq166954
    | (have j0 := eq166954 X0 x
       have j1 := eq168340 X0
       grind)
    | exact resolve eq166954 eq168340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166954 eq168340
  have eq172657 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq172594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172594
  have eq172658 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq172584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172584
  have eq172691 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq172657 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq172657
    | exact resolve eq172657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172657
  have eq189408 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = (σ (τ (k X0 (M.op X1 X1)))) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (k X1 X1))
       have i₂ := eq170679 X1 X0
       grind)
    | exact superpose eq170679 eq11
    | (have j1 := eq170679 X1 X1
       grind)
    | exact resolve eq11 eq170679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170679
  have eq189429 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189408 X0 X1
       have i₂ := eq11 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq11 eq189408
    | (have j0 := eq189408 X0 X1
       grind)
    | exact resolve eq189408 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189408
  have eq195918 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (k X0 X0) X1)
       have i₂ := eq168593 X0 X1
       grind)
    | exact superpose eq168593 eq11
    | (have j1 := eq168593 X0 X1
       grind)
    | exact resolve eq11 eq168593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168593
  have eq195934 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq195918 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq195918
    | (have j0 := eq195918 X0 X1
       grind)
    | exact resolve eq195918 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195918
  have eq196187 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34376 (k X0 X0)
       have i₂ := eq195934 X0 (k X0 X0)
       grind)
    | exact superpose eq195934 eq34376
    | (have j0 := eq34376 (k X0 X0)
       have j1 := eq195934 X0 x
       grind)
    | exact resolve eq34376 eq195934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34376 eq195934
  have eq196288 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq196187 X0
       have i₂ := eq165377 X0
       grind)
    | exact superpose eq165377 eq196187
    | (have j0 := eq196187 X0
       grind)
    | exact resolve eq196187 eq165377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165377 eq196187
  have eq196307 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq196288 X0
       have j1 := eq167421 X0
       grind)
    | (have r₁ := eq196288 X0
       have r₂ := eq167421 X0
       grind)
    | exact resolve eq196288 eq167421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196288
  have eq235105 : ∀ X0 X1 : G, (k (τ (k X0 X0)) X1) = (σ (τ (k (τ X0) X1))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (τ (k X0 X0)) X1)
       have i₂ := eq55586 X0 X1
       grind)
    | exact superpose eq55586 eq11
    | (have j1 := eq55586 X0 X1
       grind)
    | exact resolve eq11 eq55586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55586
  have eq235140 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ (k X0 X0)) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235105 X0 X1
       have i₂ := eq11 (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq235105
    | (have j0 := eq235105 X0 X1
       grind)
    | exact resolve eq235105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235105
  have eq235293 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (k (τ (σ X0)) X1) = (k (τ (k (σ X0) (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (σ X0) (σ X0)
       have i₂ := eq235140 (σ X0) X1
       grind)
    | exact superpose eq235140 eq62
    | (have j1 := eq235140 (σ X0) X1
       grind)
    | exact resolve eq62 eq235140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq235140
  have eq235302 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k (τ (σ X0)) X1) = (k (τ (k (σ X0) (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq235293 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq235293
    | (have j0 := eq235293 X0 X1
       grind)
    | exact resolve eq235293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235293
  have eq235338 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k (k (τ (σ X0)) X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235302 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq235302
    | (have j0 := eq235302 X0 X1
       grind)
    | exact resolve eq235302 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq235302
  have eq235354 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq235338
    | (have j0 := eq235338 X0 X1
       grind)
    | exact resolve eq235338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235338
  have eq235732 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq235354 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235354
  have eq235743 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq235732 X0
       have j1 := eq48714 X0
       grind)
    | (have r₁ := eq235732 X0
       have r₂ := eq48714 X0
       grind)
    | exact resolve eq235732 eq48714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48714 eq235732
  have eq236067 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9047 (k X0 X0) X0
       have i₂ := eq235743 X0
       grind)
    | exact superpose eq235743 eq9047
    | (have j0 := eq9047 (k X0 X0) X0
       grind)
    | (have r₁ := eq9047 (k X0 X0) X0
       have r₂ := eq235743 X0
       grind)
    | exact resolve eq9047 eq235743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9047 eq235743
  have eq236167 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq236067 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236067
  have eq236696 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k (k X0 X0) (M.op X0 X1)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq407 (k X0 X0) X0 X1
       have i₂ := eq236167 X0
       grind)
    | exact superpose eq236167 eq407
    | (have j0 := eq407 (k X0 X0) X0 X1
       have j1 := eq236167 X0
       grind)
    | (have r₁ := eq407 (k X0 X0) X0 x
       have r₂ := eq236167 X0
       grind)
    | exact resolve eq407 eq236167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq236709 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq236167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236167
  have eq236710 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k X0 X0) (M.op X0 X1)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq236696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236696
  have eq245467 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq169981 X0 (k X0 X0)
       have i₂ := eq172658 X0
       grind)
    | exact superpose eq172658 eq169981
    | (have j1 := eq172658 X0
       grind)
    | exact resolve eq169981 eq172658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169981 eq172658
  have eq245490 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq245467 X0
       have j1 := eq167421 X0
       grind)
    | (have r₁ := eq245467 X0
       have r₂ := eq167421 X0
       grind)
    | exact resolve eq245467 eq167421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167421 eq245467
  have eq245520 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq245490 X0
       have i₂ := eq189429 (k X0 X0) X0
       grind)
    | exact superpose eq189429 eq245490
    | (have j0 := eq245490 X0
       have j1 := eq189429 X0 X0
       grind)
    | exact resolve eq245490 eq189429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189429 eq245490
  have eq245601 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq245520 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245520
  have eq245673 : ∀ X0 : G, (k X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq245601 X0
       have i₂ := eq236710 X0 X0
       grind)
    | exact superpose eq236710 eq245601
    | (have j0 := eq245601 X0
       have j1 := eq236710 X0 x
       grind)
    | exact resolve eq245601 eq236710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236710 eq245601
  have eq245784 : ∀ X0 : G, (k X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq245673 X0
       have j1 := eq236709 X0
       grind)
    | (have r₁ := eq245673 X0
       have r₂ := eq236709 X0
       grind)
    | exact resolve eq245673 eq236709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236709 eq245673
  have eq245812 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq245784 X0
       have i₂ := eq214 X0 X0 X0
       grind)
    | exact superpose eq214 eq245784
    | (have j0 := eq245784 X0
       grind)
    | exact resolve eq245784 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245784
  have eq245907 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (k X0 X0) X1 X0
       have i₂ := eq245812 X0
       grind)
    | exact superpose eq245812 eq180
    | (have j1 := eq245812 X0
       grind)
    | exact resolve eq180 eq245812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245912 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X1 (k X0 X0) X0
       have i₂ := eq245812 X0
       grind)
    | exact superpose eq245812 eq214
    | (have j1 := eq245812 X0
       grind)
    | exact resolve eq214 eq245812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245812
  have eq246147 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq196307 X0
       have i₂ := eq245907 X0 (k X0 X0)
       grind)
    | exact superpose eq245907 eq196307
    | (have j0 := eq196307 X0
       have j1 := eq245907 X0 x
       grind)
    | exact resolve eq196307 eq245907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196307 eq245907
  have eq246336 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq246147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246147
  have eq246972 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq245912 X0 X0
       have i₂ := eq246336 X0
       grind)
    | exact superpose eq246336 eq245912
    | (have j0 := eq245912 X0 x
       have j1 := eq246336 X0
       grind)
    | exact resolve eq245912 eq246336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245912 eq246336
  have eq247055 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq246972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246972
  have eq247721 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq172691 X0
       have i₂ := eq247055 X0
       grind)
    | exact superpose eq247055 eq172691
    | exact resolve eq172691 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172691
  have eq248000 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq247055 (σ X0)
       grind)
    | exact superpose eq247055 eq15
    | exact resolve eq15 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248033 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq247055 (τ X0)
       grind)
    | exact superpose eq247055 eq39
    | exact resolve eq39 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq248234 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq248033 X0
       have i₂ := eq247055 X0
       grind)
    | exact superpose eq247055 eq248033
    | exact resolve eq248033 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248033
  have eq248262 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq248000 X0
       have i₂ := eq247055 X0
       grind)
    | exact superpose eq247055 eq248000
    | exact resolve eq248000 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247055 eq248000
  have eq250244 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (τ X0) X1 (τ X0)
       have i₂ := eq248234 X0
       grind)
    | exact superpose eq248234 eq180
    | exact resolve eq180 eq248234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250249 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X1 (τ X0) (τ X0)
       have i₂ := eq248234 X0
       grind)
    | exact superpose eq248234 eq214
    | exact resolve eq214 eq248234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248234
  have eq251842 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (σ X0) X1 (σ X0)
       have i₂ := eq248262 X0
       grind)
    | exact superpose eq248262 eq180
    | exact resolve eq180 eq248262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251847 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X1 (σ X0) (σ X0)
       have i₂ := eq248262 X0
       grind)
    | exact superpose eq248262 eq214
    | exact resolve eq214 eq248262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253965 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 (M.op X0 X1))) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250244 (M.op X0 X1) X2
       have i₂ := eq180 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq180 eq250244
    | exact resolve eq250244 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254610 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq253965 X0 X1 X2
       have i₂ := eq214 X0 X0 X1
       grind)
    | exact superpose eq214 eq253965
    | exact resolve eq253965 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253965
  have eq254824 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254610 X0 X1 X2
       have i₂ := eq250244 X0 X2
       grind)
    | exact superpose eq250244 eq254610
    | exact resolve eq254610 eq250244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250244 eq254610
  have eq255070 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250249 (M.op X0 X1) X2
       have i₂ := eq180 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq180 eq250249
    | exact resolve eq250249 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255657 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X0))) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255070 X0 X1 X2
       have i₂ := eq214 X0 X0 X1
       grind)
    | exact superpose eq214 eq255070
    | exact resolve eq255070 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255070
  have eq255789 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255657 X0 X1 X2
       have i₂ := eq250249 X0 X2
       grind)
    | exact superpose eq250249 eq255657
    | exact resolve eq255657 eq250249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250249 eq255657
  have eq256010 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq251842 (M.op X0 X1) X2
       have i₂ := eq180 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq180 eq251842
    | exact resolve eq251842 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256673 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq256010 X0 X1 X2
       have i₂ := eq214 X0 X0 X1
       grind)
    | exact superpose eq214 eq256010
    | exact resolve eq256010 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256010
  have eq256875 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq256673 X0 X1 X2
       have i₂ := eq251842 X0 X2
       grind)
    | exact superpose eq251842 eq256673
    | exact resolve eq256673 eq251842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251842 eq256673
  have eq257148 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq251847 (M.op X0 X1) X2
       have i₂ := eq180 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq180 eq251847
    | exact resolve eq251847 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257458 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9014 X0 X0 x
       have i₂ := eq251847 X0 (σ (M.op x X0))
       grind)
    | exact superpose eq251847 eq9014
    | exact resolve eq9014 eq251847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9014
  have eq257583 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq257458 X0 X1
       have i₂ := eq256875 X0 X1 (σ X1)
       grind)
    | exact superpose eq256875 eq257458
    | (have j0 := eq257458 X0 X1
       grind)
    | exact resolve eq257458 eq256875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257458
  have eq257753 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257148 X0 X1 X2
       have i₂ := eq214 X0 X0 X1
       grind)
    | exact superpose eq214 eq257148
    | exact resolve eq257148 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257148
  have eq257812 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq257583 X0 X1
       have i₂ := eq256875 X0 X1 (σ X1)
       grind)
    | exact superpose eq256875 eq257583
    | (have j0 := eq257583 X0 X1
       grind)
    | exact resolve eq257583 eq256875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257583
  have eq257893 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257753 X0 X1 X2
       have i₂ := eq251847 X0 X2
       grind)
    | exact superpose eq251847 eq257753
    | exact resolve eq257753 eq251847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251847 eq257753
  have eq359494 : ∀ X0 X1 X2 : G, (M.op (τ (σ (M.op X0 X0))) X2) = (M.op (τ (σ X1)) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254824 (σ X1) (σ X0) X2
       have i₂ := eq257812 X1 X0
       grind)
    | exact superpose eq257812 eq254824
    | (have j1 := eq257812 X1 X0
       grind)
    | exact resolve eq254824 eq257812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254824
  have eq359495 : ∀ X0 X1 X2 : G, (M.op X1 (τ (σ (M.op X0 X0)))) = (M.op X1 (τ (σ X2))) ∨ (σ (M.op X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255789 (σ X2) (σ X0) X1
       have i₂ := eq257812 X2 X0
       grind)
    | exact superpose eq257812 eq255789
    | (have j1 := eq257812 X2 X0
       grind)
    | exact resolve eq255789 eq257812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255789 eq257812
  have eq359583 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (τ (σ (M.op X0 X0)))) ∨ (σ (M.op X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359495 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq359495
    | (have j0 := eq359495 X0 X1 X2
       grind)
    | exact resolve eq359495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359495
  have eq359584 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (τ (σ (M.op X0 X0))) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359494 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq359494
    | (have j0 := eq359494 X0 X1 X2
       grind)
    | exact resolve eq359494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359494
  have eq359668 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 X0)) ∨ (σ (M.op X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359583 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq359583
    | (have j0 := eq359583 X0 X1 X2
       grind)
    | exact resolve eq359583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359583
  have eq359669 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359584 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq359584
    | (have j0 := eq359584 X0 X1 X2
       grind)
    | exact resolve eq359584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359584
  have eq359701 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (σ (M.op X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359668 X0 X1 X2
       have i₂ := eq214 X1 X0 X0
       grind)
    | exact superpose eq214 eq359668
    | (have j0 := eq359668 X0 X1 X2
       grind)
    | exact resolve eq359668 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq359668
  have eq359702 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359669 X0 X1 X2
       have i₂ := eq180 X0 X2 X0
       grind)
    | exact superpose eq180 eq359669
    | (have j0 := eq359669 X0 X1 X2
       grind)
    | exact resolve eq359669 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq359669
  have eq360367 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq359701 y X0 x
       grind)
    | exact superpose eq359701 eq16
    | (have j1 := eq359701 y X0 x
       grind)
    | (have r₁ := eq16
       have r₂ := eq359701 y x x
       grind)
    | exact resolve eq16 eq359701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359701
  have eq360503 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq360367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360367
  have eq369274 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq359702 y x X0
       grind)
    | exact superpose eq359702 eq16
    | (have j1 := eq359702 y x X0
       grind)
    | (have r₁ := eq16
       have r₂ := eq359702 y x x
       grind)
    | exact resolve eq16 eq359702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359702
  have eq369415 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq369274 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369274
  have eq370823 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq247721 y
       have i₂ := eq369415 y
       grind)
    | exact superpose eq369415 eq247721
    | exact resolve eq247721 eq369415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247721
  have eq371073 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq257893 y X0 X1
       have i₂ := eq369415 X0
       grind)
    | exact superpose eq369415 eq257893
    | exact resolve eq257893 eq369415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369415
  have eq371595 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq371073 x X1
       have i₂ := eq257893 x x X1
       grind)
    | exact superpose eq257893 eq371073
    | exact resolve eq371073 eq257893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257893 eq371073
  have eq371773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq370823
       have i₂ := eq256875 x y (σ y)
       grind)
    | exact superpose eq256875 eq370823
    | exact resolve eq370823 eq256875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256875 eq370823
  have eq372372 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq371773
       have r₂ := eq16
       grind)
    | exact resolve eq371773 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371773
  have eq372666 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq372372
       have i₂ := eq360503 x
       grind)
    | exact superpose eq360503 eq372372
    | exact resolve eq372372 eq360503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372372
  have eq377659 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq371595 (σ x)
       grind)
    | exact superpose eq371595 eq16
    | exact resolve eq16 eq371595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371595
  have eq377956 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq377659
       have i₂ := eq248262 x
       grind)
    | exact superpose eq248262 eq377659
    | exact resolve eq377659 eq248262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248262 eq377659
  have eq378457 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq377956
       have i₂ := eq372666
       grind)
    | exact superpose eq372666 eq377956
    | exact resolve eq377956 eq372666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377956
  have eq378829 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq378457
       have i₂ := eq360503 x
       grind)
    | exact superpose eq360503 eq378457
    | exact resolve eq378457 eq360503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360503 eq378457
  have eq379116 : False := by grind
  exact eq379116

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation3744 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq9 X0 X1 x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq25 x X1 X2 X3 x
       have i₂ := eq9 X2 X1 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq27 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24 X0 x X2 X3 x
       have i₂ := eq9 X0 X3 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X2) X1
       have i₂ := eq27 X0 X2 X1
       grind)
    | exact superpose eq27 eq13
    | (have j0 := eq13 (M.op X0 X2) X1
       grind)
    | (have r₁ := eq13 (M.op X0 x) x
       have r₂ := eq27 X0 x x
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq58 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq62 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq63
  have eq72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq27
    | exact resolve eq27 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26
    | exact resolve eq26 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 (σ X2) X1 (σ X0)
       have i₂ := eq56 X2 X0
       grind)
    | exact superpose eq56 eq26
    | (have j1 := eq56 X2 X0
       grind)
    | exact resolve eq26 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq110 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | exact resolve eq111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq124 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) X1)) = (k (M.op X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 : G, (σ (k X1 (M.op (τ X0) (τ X0)))) = (k (σ X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op (τ X0) (τ X0))
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1360 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq165 X0 (τ X0)
       have i₂ := eq1136 (τ X0) (τ X0)
       grind)
    | exact superpose eq1136 eq165
    | (have j1 := eq1136 (τ X0) (τ X0)
       grind)
    | exact resolve eq165 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1409 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1360 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1360
    | (have j0 := eq1360 X0
       grind)
    | exact resolve eq1360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1420 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1409 X0
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq1409
    | (have j0 := eq1409 X0
       grind)
    | exact resolve eq1409 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1509 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) (σ (τ X0))) ∨ (τ (τ X0)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq165 X0 (τ X0)
       have i₂ := eq1420 (τ X0)
       grind)
    | exact superpose eq1420 eq165
    | (have j1 := eq1420 (τ X0)
       grind)
    | exact resolve eq165 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq1420
  have eq1527 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (τ X0)) = (τ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1509 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1509
    | (have j0 := eq1509 X0
       grind)
    | exact resolve eq1509 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1548 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1527 X0
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq1527
    | (have j0 := eq1527 X0
       grind)
    | exact resolve eq1527 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1785 : ∀ X0 X1 : G, (σ (k X1 (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k X1 (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq116
    | exact resolve eq116 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1837 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (k X1 (M.op (τ X0) (τ X0)))) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k X1 (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1785 X0 X1
       have i₂ := eq27 X0 X0 (σ X1)
       grind)
    | exact superpose eq27 eq1785
    | (have j0 := eq1785 X0 X1
       grind)
    | exact resolve eq1785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1785
  have eq1843 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (k (σ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k X1 (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1837 X0 X1
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq1837
    | (have j0 := eq1837 X0 X1
       grind)
    | exact resolve eq1837 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq1847 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (k (σ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1843 X0 X1
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq1843
    | (have j0 := eq1843 X0 X1
       grind)
    | exact resolve eq1843 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq2415 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq106 y (σ x) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq106 X0 (σ x) y
       grind)
    | exact superpose eq106 eq16
    | (have j1 := eq106 y x X0
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2464 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq106 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2468 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2464 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq2464
    | (have j0 := eq2464 X0 X1
       grind)
    | exact resolve eq2464 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464
  have eq6463 : ∀ X0 X1 : G, (τ (k (τ (M.op X0 X0)) X1)) = (k (τ (τ X0)) (τ X1)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq124 X1 (τ (M.op X0 X0))
       have i₂ := eq1548 X0
       grind)
    | exact superpose eq1548 eq124
    | (have j1 := eq1548 X0
       grind)
    | exact resolve eq124 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq6514 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (k (τ (M.op X0 X0)) X1)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6463 X0 X1
       have i₂ := eq124 X1 (τ X0)
       grind)
    | exact superpose eq124 eq6463
    | (have j0 := eq6463 X0 X1
       grind)
    | exact resolve eq6463 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq6463
  have eq23656 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) ≠ (σ (M.op (M.op (τ X1) (τ X1)) (M.op (τ X1) (τ X1)))) ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (σ X0)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2468 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq2468
    | (have j0 := eq2468 X0 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq2468 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq2468
  have eq23703 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (σ X0)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23656 X0 X1
       have i₂ := eq9 (τ X1) (τ X1) (τ X1) (τ X1)
       grind)
    | exact superpose eq9 eq23656
    | (have j0 := eq23656 X0 X1
       grind)
    | exact resolve eq23656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23656
  have eq23758 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k (σ X0) (M.op X1 X1)) ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (σ X0)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23703 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq23703
    | (have j0 := eq23703 X0 X1
       grind)
    | exact resolve eq23703 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23703
  have eq23802 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) ≠ (k (σ X0) (M.op X1 X1)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23758 X0 X1
       have i₂ := eq80 (τ X1) (σ X0)
       grind)
    | exact superpose eq80 eq23758
    | (have j0 := eq23758 X0 X1
       grind)
    | exact resolve eq23758 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq23758
  have eq23837 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 X1)) ∨ (M.op X1 X1) ≠ (k (σ X0) (M.op X1 X1)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23802 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq23802
    | (have j0 := eq23802 X0 X1
       grind)
    | exact resolve eq23802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23802
  have eq23866 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 X1)) ∨ (M.op X1 X1) ≠ (k (σ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23837 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq23837
    | (have j0 := eq23837 X0 X1
       grind)
    | exact resolve eq23837 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq23837
  have eq23888 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq23866 X0 X1
       have j1 := eq1847 X1 X0
       grind)
    | (have r₁ := eq23866 X1 (σ X1)
       have r₂ := eq1847 (σ X1) X1
       grind)
    | (have r₁ := eq23866 X1 X0
       have r₂ := eq1847 X0 X1
       grind)
    | exact resolve eq23866 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847 eq23866
  have eq24549 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23888 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23888
    | exact resolve eq23888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24634 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 X0))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 X0)
       have i₂ := eq23888 X1 X0
       grind)
    | exact superpose eq23888 eq72
    | (have j1 := eq23888 X1 X0
       grind)
    | exact resolve eq72 eq23888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq23888
  have eq25011 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (k X1 (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24549 X0 (τ X0)
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq24549
    | exact resolve eq24549 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq24549
  have eq32790 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25011 X0 X1
       have i₂ := eq24634 X0 X1
       grind)
    | exact superpose eq24634 eq25011
    | (have j0 := eq25011 X0 X1
       have j1 := eq24634 X0 X1
       grind)
    | exact resolve eq25011 eq24634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24634 eq25011
  have eq38946 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2415 x
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq2415
    | (have j0 := eq2415 x
       grind)
    | exact resolve eq2415 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq197809 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (σ (τ (k (τ X0) X1))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (τ (M.op X0 X0)) X1)
       have i₂ := eq6514 X0 X1
       grind)
    | exact superpose eq6514 eq11
    | (have j1 := eq6514 X0 X1
       grind)
    | exact resolve eq11 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq197824 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ (M.op X0 X0)) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq197809 X0 X1
       have i₂ := eq11 (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq197809
    | (have j0 := eq197809 X0 X1
       grind)
    | exact resolve eq197809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197809
  have eq199574 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k (σ (τ (M.op X0 X0))) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ (M.op X0 X0))
       have i₂ := eq197824 X0 (τ X1)
       grind)
    | exact superpose eq197824 eq19
    | (have j1 := eq197824 X0 X1
       grind)
    | exact resolve eq19 eq197824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197824
  have eq199603 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X1))) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199574 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq199574
    | (have j0 := eq199574 X0 X1
       grind)
    | exact resolve eq199574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199574
  have eq199666 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199603 X0 X1
       have i₂ := eq19 X1 (τ X0)
       grind)
    | exact superpose eq19 eq199603
    | (have j0 := eq199603 X0 X1
       grind)
    | exact resolve eq199603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq199603
  have eq199678 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq199666
    | (have j0 := eq199666 X0 X1
       grind)
    | exact resolve eq199666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199666
  have eq200349 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq199678 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199678
  have eq200351 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  clear eq200349
  have eq200425 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq200351 X0
       have j1 := eq1136 X0 X0
       grind)
    | (have r₁ := eq200351 x
       have r₂ := eq1136 x x
       grind)
    | exact resolve eq200351 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq200351
  have eq459564 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32790 X0 X1
       grind)
    | exact superpose eq32790 eq10
    | (have j1 := eq32790 X0 X1
       grind)
    | exact resolve eq10 eq32790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32790
  have eq459567 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq459564 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459564
  have eq459592 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq459567 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq459567
    | (have j0 := eq459567 (σ X0) X1
       grind)
    | exact resolve eq459567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459567
  have eq459738 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq459592 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq459592
    | (have j0 := eq459592 X0 X1
       grind)
    | exact resolve eq459592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459592
  have eq459757 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq459738 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq459738
    | (have j0 := eq459738 X0 X1
       grind)
    | exact resolve eq459738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459738
  have eq459910 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq459757 X0 X1
       grind)
    | exact superpose eq459757 eq11
    | (have j1 := eq459757 X0 X1
       grind)
    | exact resolve eq11 eq459757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459757
  have eq460372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq459910 x y
       grind)
    | exact superpose eq459910 eq16
    | (have j1 := eq459910 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq459910 x y
       grind)
    | exact resolve eq16 eq459910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459910
  have eq460750 : y = (M.op x x) := by grind
  clear eq460372
  have eq460900 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq81 x X0
       have i₂ := eq460750
       grind)
    | exact superpose eq460750 eq81
    | exact resolve eq81 eq460750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq461254 : x = (k y x) := by
    first
    | (have i₁ := eq200425 x
       have i₂ := eq460750
       grind)
    | exact superpose eq460750 eq200425
    | exact resolve eq200425 eq460750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200425
  have eq461349 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq26 x X0 x
       have i₂ := eq460750
       grind)
    | exact superpose eq460750 eq26
    | exact resolve eq26 eq460750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq463031 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38946
       have i₂ := eq461349 x
       grind)
    | exact superpose eq461349 eq38946
    | exact resolve eq38946 eq461349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38946
  have eq463112 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq463031
  have eq463125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq463112
       have i₂ := eq461254
       grind)
    | exact superpose eq461254 eq463112
    | exact resolve eq463112 eq461254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461254 eq463112
  have eq463798 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq463125
       have i₂ := eq460900 (σ x)
       grind)
    | exact superpose eq460900 eq463125
    | exact resolve eq463125 eq460900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460900 eq463125
  have eq464097 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq463798
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq463798
    | exact resolve eq463798 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463798
  have eq464337 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq464097
       have i₂ := eq460750
       grind)
    | exact superpose eq460750 eq464097
    | exact resolve eq464097 eq460750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464097
  have eq464338 : (σ x) = (σ y) := by grind
  clear eq464337
  have eq464762 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464338
       grind)
    | exact superpose eq464338 eq16
    | exact resolve eq16 eq464338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465237 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq464762
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq464762
    | exact resolve eq464762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq464762
  have eq465284 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq465237
       have i₂ := eq460750
       grind)
    | exact superpose eq460750 eq465237
    | exact resolve eq465237 eq460750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465237
  have eq465314 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq465284
       have i₂ := eq464338
       grind)
    | exact superpose eq464338 eq465284
    | exact resolve eq465284 eq464338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465284
  have eq465339 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq465314
       have i₂ := eq461349 x
       grind)
    | exact superpose eq461349 eq465314
    | exact resolve eq465314 eq461349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461349 eq465314
  have eq465359 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq465339
       have i₂ := eq460750
       grind)
    | exact superpose eq460750 eq465339
    | exact resolve eq465339 eq460750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460750 eq465339
  have eq465375 : False := by grind
  exact eq465375
