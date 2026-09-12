import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq22
    | exact resolve eq22 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq185 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq172
    | (have j0 := eq172 X0
       grind)
    | exact resolve eq172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq172
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq185 X0
       have j1 := eq12 (σ (τ X0)) X0
       grind)
    | (have r₁ := eq185 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq185 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq187 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq186
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq194 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq187 (σ X0)
       grind)
    | exact superpose eq187 eq15
    | exact resolve eq15 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq187 X0
       grind)
    | exact superpose eq187 eq194
    | exact resolve eq194 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq194
  have eq230 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X0) X1
       have i₂ := eq201 X0
       grind)
    | exact superpose eq201 eq26
    | exact resolve eq26 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq240 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq256 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq240
       have i₂ := eq201 y
       grind)
    | exact superpose eq201 eq240
    | exact resolve eq240 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq256
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq256
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq256
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq256
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq256 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1566 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1565
  have eq15955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1566
       grind)
    | exact superpose eq1566 eq16
    | exact resolve eq16 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq15956 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15955
       have r₂ := eq201 x
       grind)
    | exact resolve eq15955 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq15958 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15956
       grind)
    | exact superpose eq15956 eq10
    | exact resolve eq10 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15956
  have eq16037 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15958
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15958
    | exact resolve eq15958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15958
  have eq16044 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16037
       grind)
    | exact superpose eq16037 eq16
    | exact resolve eq16 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16037
  have eq16045 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq16044
       have r₂ := eq201 x
       grind)
    | exact resolve eq16044 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq16044
  have eq16316 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq16045
       grind)
    | exact superpose eq16045 eq10
    | exact resolve eq10 eq16045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16045
  have eq16397 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16316
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16316
    | exact resolve eq16316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16316
  have eq16398 : y = (M.op y y) := by grind
  clear eq16397
  have eq16423 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq230 y X0
       have i₂ := eq16398
       grind)
    | exact superpose eq16398 eq230
    | exact resolve eq230 eq16398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq16494 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq106 X0 y y
       have i₂ := eq16398
       grind)
    | exact superpose eq16398 eq106
    | exact resolve eq106 eq16398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq16398
  have eq16531 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16494 x
       have i₂ := eq22 y x
       grind)
    | exact superpose eq22 eq16494
    | exact resolve eq16494 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16494
  have eq16587 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16423 X0
       have i₂ := eq22 (σ y) X0
       grind)
    | exact superpose eq22 eq16423
    | exact resolve eq16423 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423
  have eq18350 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq16587 X0
       grind)
    | exact superpose eq16587 eq22
    | exact resolve eq22 eq16587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16587
  have eq20778 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18350 (σ x)
       grind)
    | exact superpose eq18350 eq16
    | exact resolve eq16 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18350
  have eq20814 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq20778
       have i₂ := eq16531 x
       grind)
    | exact superpose eq16531 eq20778
    | exact resolve eq20778 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531 eq20778
  have eq20815 : False := by grind
  exact eq20815

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pyy_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq22
    | exact resolve eq22 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq185 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq172
    | (have j0 := eq172 X0
       grind)
    | exact resolve eq172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq172
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq185 X0
       have j1 := eq12 (σ (τ X0)) X0
       grind)
    | (have r₁ := eq185 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq185 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq187 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq186
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq194 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq187 (σ X0)
       grind)
    | exact superpose eq187 eq15
    | exact resolve eq15 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq187 X0
       grind)
    | exact superpose eq187 eq194
    | exact resolve eq194 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq194
  have eq230 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X0) X1
       have i₂ := eq201 X0
       grind)
    | exact superpose eq201 eq26
    | exact resolve eq26 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq240 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq256 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq240
       have i₂ := eq201 y
       grind)
    | exact superpose eq201 eq240
    | exact resolve eq240 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq256
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq256
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq256
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq256
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq256 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1566 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1565
  have eq15955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1566
       grind)
    | exact superpose eq1566 eq16
    | exact resolve eq16 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq15956 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15955
       have r₂ := eq201 x
       grind)
    | exact resolve eq15955 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq15958 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15956
       grind)
    | exact superpose eq15956 eq10
    | exact resolve eq10 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15956
  have eq16037 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15958
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15958
    | exact resolve eq15958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15958
  have eq16044 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16037
       grind)
    | exact superpose eq16037 eq16
    | exact resolve eq16 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16037
  have eq16045 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq16044
       have r₂ := eq201 x
       grind)
    | exact resolve eq16044 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq16044
  have eq16316 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq16045
       grind)
    | exact superpose eq16045 eq10
    | exact resolve eq10 eq16045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16045
  have eq16397 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16316
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16316
    | exact resolve eq16316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16316
  have eq16398 : y = (M.op y y) := by grind
  clear eq16397
  have eq16423 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq230 y X0
       have i₂ := eq16398
       grind)
    | exact superpose eq16398 eq230
    | exact resolve eq230 eq16398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq16494 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq106 X0 y y
       have i₂ := eq16398
       grind)
    | exact superpose eq16398 eq106
    | exact resolve eq106 eq16398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq16398
  have eq16531 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16494 x
       have i₂ := eq22 y x
       grind)
    | exact superpose eq22 eq16494
    | exact resolve eq16494 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16494
  have eq16587 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16423 X0
       have i₂ := eq22 (σ y) X0
       grind)
    | exact superpose eq22 eq16423
    | exact resolve eq16423 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423
  have eq18350 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq16587 X0
       grind)
    | exact superpose eq16587 eq22
    | exact resolve eq22 eq16587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16587
  have eq20778 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18350 (σ x)
       grind)
    | exact superpose eq18350 eq16
    | exact resolve eq16 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18350
  have eq20814 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq20778
       have i₂ := eq16531 x
       grind)
    | exact superpose eq16531 eq20778
    | exact resolve eq20778 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531 eq20778
  have eq20815 : False := by grind
  exact eq20815

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pxy_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq44 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq9
    | exact resolve eq9 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq44
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq145 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq179 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x (M.op x x)
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2496 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq179
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq179
    | (have j1 := eq14 x (M.op x x)
       grind)
    | (have r₁ := eq179
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq179
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq179 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2497 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq2496
  have eq17443 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2497
       grind)
    | exact superpose eq2497 eq16
    | exact resolve eq16 eq2497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq17444 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17443
       have r₂ := eq22 x
       grind)
    | exact resolve eq17443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17443
  have eq17446 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17444
       grind)
    | exact superpose eq17444 eq10
    | exact resolve eq10 eq17444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17444
  have eq17518 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17446
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17446
    | exact resolve eq17446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17446
  have eq17520 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17518
       grind)
    | exact superpose eq17518 eq16
    | exact resolve eq16 eq17518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17518
  have eq17521 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17520
       have r₂ := eq22 x
       grind)
    | exact resolve eq17520 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17520
  have eq17717 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq17521
       grind)
    | exact superpose eq17521 eq10
    | exact resolve eq10 eq17521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17521
  have eq17790 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17717
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17717
    | exact resolve eq17717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17717
  have eq17791 : x = (M.op x x) := by grind
  clear eq17790
  have eq17821 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq145 x X0
       have i₂ := eq17791
       grind)
    | exact superpose eq17791 eq145
    | exact resolve eq145 eq17791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq17897 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48 x x X0
       have i₂ := eq17791
       grind)
    | exact superpose eq17791 eq48
    | exact resolve eq48 eq17791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq17791
  have eq17964 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17897 X0
       have i₂ := eq44 x X0
       grind)
    | exact superpose eq44 eq17897
    | exact resolve eq17897 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17897
  have eq18018 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17821 X0
       have i₂ := eq44 (σ x) X0
       grind)
    | exact superpose eq44 eq17821
    | exact resolve eq17821 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq17821
  have eq19387 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18018 (σ y)
       grind)
    | exact superpose eq18018 eq16
    | exact resolve eq16 eq18018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq19584 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq19387
       have i₂ := eq17964 y
       grind)
    | exact superpose eq17964 eq19387
    | exact resolve eq19387 eq17964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17964 eq19387
  have eq19585 : False := by grind
  exact eq19585

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pxy_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq111 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq511 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
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
  have eq514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq509
    | (have j0 := eq509 X0 X1
       grind)
    | exact resolve eq509 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq2189 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq514 x y
       grind)
    | exact superpose eq514 eq16
    | (have j1 := eq514 x y
       grind)
    | exact resolve eq16 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq29712 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq511
    | exact resolve eq511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq29841 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29712 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq29712
    | (have j0 := eq29712 X0 X1
       grind)
    | exact resolve eq29712 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29712
  have eq44021 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2189
       have i₂ := eq29841 x y
       grind)
    | exact superpose eq29841 eq2189
    | (have j1 := eq29841 x y
       grind)
    | (have r₁ := eq2189
       have r₂ := eq29841 x y
       grind)
    | (have r₁ := eq2189
       have r₂ := eq29841 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2189
       have r₂ := eq29841 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2189 eq29841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189 eq29841
  have eq44022 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq44021
  have eq66419 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44022
       grind)
    | exact superpose eq44022 eq16
    | exact resolve eq16 eq44022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44022
  have eq66420 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq66419
       have r₂ := eq23 x
       grind)
    | exact resolve eq66419 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66419
  have eq66422 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq66420
       grind)
    | exact superpose eq66420 eq10
    | exact resolve eq10 eq66420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66420
  have eq66515 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq66422
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66422
    | exact resolve eq66422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66422
  have eq66517 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66515
       grind)
    | exact superpose eq66515 eq16
    | exact resolve eq16 eq66515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66515
  have eq66518 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq66517
       have r₂ := eq23 x
       grind)
    | exact resolve eq66517 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq66517
  have eq66568 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq66518
       grind)
    | exact superpose eq66518 eq10
    | exact resolve eq10 eq66518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66518
  have eq66661 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66568
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66568
    | exact resolve eq66568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66568
  have eq66662 : x = (M.op y y) := by grind
  clear eq66661
  have eq66668 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq66662
       grind)
    | exact superpose eq66662 eq112
    | exact resolve eq112 eq66662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq66959 : y = (M.op x y) := by
    first
    | (have i₁ := eq111 y y
       have i₂ := eq66662
       grind)
    | exact superpose eq66662 eq111
    | exact resolve eq111 eq66662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq66662
  have eq67133 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66668
       grind)
    | exact superpose eq66668 eq16
    | exact resolve eq16 eq66668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66668
  have eq67200 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq67133
       have i₂ := eq66959
       grind)
    | exact superpose eq66959 eq67133
    | exact resolve eq67133 eq66959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66959 eq67133
  have eq67201 : False := by grind
  exact eq67201

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pxy_pxy_pyx_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq181 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq184 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op x y) x) y) X0
       have r₂ := eq175 X0
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op x y) x) y)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (k (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq188 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0
       have r₂ := eq176 X0
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (k (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq338 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq385 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (M.op (M.op x y) x) y)) X0) := by
    intro X0
    first
    | exact superpose eq186 eq39
    | exact resolve eq39 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq419 : ∀ X0 : G, (k (σ (M.op (M.op (M.op x y) x) y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq385
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq718 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq28
    | (have j0 := eq28 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq720 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq726 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq727 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq779 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq728 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq728 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq728 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq780 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq779 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq779 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq779 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq839 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op X1 X2) X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq182 (σ X0) X1 X2
       grind)
    | exact superpose eq182 eq338
    | exact resolve eq338 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq840 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op (M.op X1 X2) X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq182 (τ X0) X1 X2
       grind)
    | exact superpose eq182 eq39
    | exact resolve eq39 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq182
  have eq854 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op (M.op X1 X2) X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq840 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq840
    | exact resolve eq840 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq855 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X1 X2) X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq839 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq839
    | exact resolve eq839 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1075 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq780 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq780
    | exact resolve eq780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq1172 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq40
    | exact resolve eq40 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq726
  have eq1174 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1172
    | exact resolve eq1172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1176 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1174
    | exact resolve eq1174 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1176 eq727
    | exact resolve eq727 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1844 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1836
       have r₂ := eq27
       grind)
    | exact resolve eq1836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1849 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1844 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1844
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1844
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1844
       grind)
    | exact resolve eq13 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1850 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1844 eq16
    | exact resolve eq16 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1862 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq1849
  have eq1873 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq1850
    | (have j0 := eq1850 X0
       grind)
    | exact resolve eq1850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq1939 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)) = (M.op X0 (M.op (M.op X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X0 (M.op (M.op X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)
       have i₂ := eq177 X1 X2 X3 X0
       grind)
    | exact superpose eq177 eq28
    | (have j0 := eq28 X0 (M.op (M.op X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)
       grind)
    | (have r₁ := eq28 X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)
       have r₂ := eq177 X0 X1 X2 X3
       grind)
    | exact resolve eq28 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1951 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)) = (M.op X0 (M.op (M.op X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1939 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1964 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (k X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)) = (k X0 (M.op (k X1 (M.op (M.op (M.op X2 X3) X2) X3)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1951 X0 X0 X1 X2
       have i₂ := eq725 X0 X1 X2
       grind)
    | exact superpose eq725 eq1951
    | exact resolve eq1951 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2095 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1862 eq1176
    | exact resolve eq1176 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq1862
  have eq2103 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2095
  have eq2115 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq2103
       grind)
    | exact superpose eq2103 eq16
    | exact resolve eq16 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2116 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq2103
       grind)
    | exact superpose eq2103 eq28
    | (have j0 := eq28 x y
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq2103
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq2103
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq2103
       grind)
    | exact resolve eq28 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq2127 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2116
  have eq2139 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2127
    | exact resolve eq2127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2140 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2115 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2115
    | (have j0 := eq2115 X0
       grind)
    | exact resolve eq2115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2141 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2139
       have r₂ := eq179
       grind)
    | exact resolve eq2139 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq2139
  have eq2149 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 (M.op (M.op X2 (M.op (M.op (M.op X3 X4) X3) X4)) X2)) X0)) = (k X1 (M.op (M.op X0 (M.op (M.op X2 (M.op (M.op (M.op X3 X4) X3) X4)) X2)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq725 X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X3
       have i₂ := eq177 X0 X1 X2 X3
       grind)
    | exact superpose eq177 eq725
    | exact resolve eq725 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2174 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq725 X0 X1 X2
       grind)
    | exact superpose eq725 eq177
    | exact resolve eq177 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2273 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 (M.op (k X2 (M.op (M.op (M.op X3 X4) X3) X4)) X2)) X0)) = (k X1 (M.op (M.op X0 (M.op (k X2 (M.op (M.op (M.op X3 X4) X3) X4)) X2)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2149 X0 X1 X0 X1 X2
       have i₂ := eq725 X0 X1 X2
       grind)
    | exact superpose eq725 eq2149
    | exact resolve eq2149 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2309 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (k X0 (M.op (k X2 (M.op (M.op (M.op X3 X4) X3) X4)) X2)) X0)) = (k X1 (M.op (k X0 (M.op (k X2 (M.op (M.op (M.op X3 X4) X3) X4)) X2)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2273 X0 X1 X1 X2 X3
       have i₂ := eq1964 X0 X1 X2 X3
       grind)
    | exact superpose eq1964 eq2273
    | exact resolve eq2273 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq2273
  have eq2315 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq2141
       grind)
    | exact superpose eq2141 eq41
    | exact resolve eq41 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2141
  have eq2319 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2315
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2315
    | exact resolve eq2315 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq2321 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2319
    | exact resolve eq2319 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2500 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2140 eq419
    | exact resolve eq419 eq2140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq2140
  have eq2561 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2500 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2500
    | (have j0 := eq2500 X0
       grind)
    | exact resolve eq2500 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2634 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2561 eq770
    | (have j0 := eq770 (σ y)
       grind)
    | (have r₁ := eq770 (σ y)
       have r₂ := eq2561 (σ y)
       grind)
    | exact resolve eq770 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2647 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2634
  have eq2675 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = (k X0 (M.op (M.op (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2647 eq725
    | exact resolve eq725 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2695 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (k X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2647 eq2675
    | exact resolve eq2675 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675
  have eq2707 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2647 eq2695
    | exact resolve eq2695 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647 eq2695
  have eq4212 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2707 eq26
    | (have j1 := eq2707 (σ x)
       grind)
    | exact resolve eq26 eq2707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq4233 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4212
       have r₂ := eq180
       grind)
    | exact resolve eq4212 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq4212
  have eq4347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4233 eq2321
    | exact resolve eq2321 eq4233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321 eq4233
  have eq4354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4347
  have eq4360 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4354
       have r₂ := eq27
       grind)
    | exact resolve eq4354 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4354
  have eq4367 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4360 eq176
    | exact resolve eq176 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4387 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4360 eq719
    | (have r₁ := eq719
       have r₂ := eq4360
       grind)
    | exact resolve eq719 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4401 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4387
  have eq4423 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4401 eq4367
    | exact resolve eq4367 eq4401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq4646 : ∀ X0 : G, (k (τ (M.op (M.op (k (σ y) (σ x)) (σ y)) (σ x))) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4401 eq855
    | exact resolve eq855 eq4401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4401
  have eq4653 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4423 eq4646
    | exact resolve eq4646 eq4423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4423 eq4646
  have eq4668 : ∀ X0 : G, (k x X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq4653
    | exact resolve eq4653 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653
  have eq4993 : x ≠ x ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq770 x
       have i₂ := eq4668 x
       grind)
    | exact superpose eq4668 eq770
    | (have j0 := eq770 x
       grind)
    | (have r₁ := eq770 x
       have r₂ := eq4668 x
       grind)
    | exact resolve eq770 eq4668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4668
  have eq5008 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4993
  have eq5036 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq5008
       grind)
    | exact superpose eq5008 eq16
    | exact resolve eq16 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5067 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5008 eq5036
    | exact resolve eq5036 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036
  have eq5080 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5008 eq5067
    | exact resolve eq5067 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5008 eq5067
  have eq5092 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5080 y
       grind)
    | exact superpose eq5080 eq18
    | (have j1 := eq5080 y
       grind)
    | exact resolve eq18 eq5080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq5121 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq5092
  have eq5142 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5121 eq29
    | exact resolve eq29 eq5121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq5174 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq5142
    | exact resolve eq5142 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq5178 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5174
       grind)
    | exact superpose eq5174 eq24
    | exact resolve eq24 eq5174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5181 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) (M.op x y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq5174
       grind)
    | exact superpose eq5174 eq175
    | exact resolve eq175 eq5174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5203 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq718
       have i₂ := eq5174
       grind)
    | exact superpose eq5174 eq718
    | (have r₁ := eq718
       have r₂ := eq5174
       grind)
    | exact resolve eq718 eq5174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq5174
  have eq5218 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq5203
  have eq5238 : ∀ X0 : G, (M.op (M.op (k (M.op x y) x) (M.op x y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5218 eq5181
    | exact resolve eq5181 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq5241 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5178
    | exact resolve eq5178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178
  have eq5863 : ∀ X0 : G, (k (σ (M.op (M.op (k (M.op x y) x) (M.op x y)) x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5218 eq854
    | exact resolve eq854 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq5218
  have eq5868 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5238 eq5863
    | exact resolve eq5863 eq5238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5238 eq5863
  have eq5909 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5868 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5868
    | (have j0 := eq5868 X0
       grind)
    | exact resolve eq5868 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5868
  have eq6034 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5909 eq770
    | (have j0 := eq770 (σ x)
       grind)
    | (have r₁ := eq770 (σ x)
       have r₂ := eq5909 (σ x)
       grind)
    | exact resolve eq770 eq5909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq5909
  have eq6050 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6034
  have eq6075 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6050 eq16
    | exact resolve eq16 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6106 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6050 eq6075
    | exact resolve eq6075 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6075
  have eq6119 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6050 eq6106
    | exact resolve eq6106 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050 eq6106
  have eq6133 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6119 eq26
    | (have j1 := eq6119 (σ y)
       grind)
    | exact resolve eq26 eq6119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6119
  have eq6182 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6133 eq27
    | exact resolve eq27 eq6133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6133
  have eq6245 : x = (M.op x y) := by
    first
    | (have r₁ := eq6182
       have r₂ := eq5241
       grind)
    | exact resolve eq6182 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241 eq6182
  have eq6253 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6245
       grind)
    | exact superpose eq6245 eq18
    | exact resolve eq18 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6254 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6245
       grind)
    | exact superpose eq6245 eq22
    | exact resolve eq22 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6257 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq6245
       grind)
    | exact superpose eq6245 eq175
    | exact resolve eq175 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq6258 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op x y) (M.op x y)) y)) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq6245
       grind)
    | exact superpose eq6245 eq185
    | exact resolve eq185 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq6303 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6254 eq20
    | exact resolve eq20 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6389 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq6253 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6394 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) (M.op x y)) y)) = (k X0 (M.op (M.op (M.op x y) (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq6253 eq725
    | exact resolve eq725 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq17575 : ∀ X0 X1 : G, (M.op (M.op (k X0 (M.op (M.op (M.op x y) (M.op x y)) y)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq6394 eq6258
    | exact resolve eq6258 eq6394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6258 eq6394
  have eq17844 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) y) (τ (M.op (M.op (M.op X0 X1) X0) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17575 (τ (M.op (M.op (M.op X1 X2) X1) X2)) X1
       have i₂ := eq855 (M.op (M.op sF0 sF0) y) X1 X2
       grind)
    | exact superpose eq855 eq17575
    | exact resolve eq17575 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq17575
  have eq17950 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op (M.op X0 X1) X0) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq6257 eq17844
    | exact resolve eq17844 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6257 eq17844
  have eq586141 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1873 eq190
    | exact resolve eq190 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq1873
  have eq586950 : ∀ X0 : G, (M.op x y) = (M.op y (M.op x y)) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq586141 X0
       have i₂ := eq6245
       grind)
    | exact superpose eq6245 eq586141
    | (have j0 := eq586141 X0
       grind)
    | exact resolve eq586141 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586141
  have eq587275 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq586950 (M.op x X0)
       grind)
    | exact superpose eq586950 eq28
    | (have j0 := eq28 (M.op x y) y
       have j1 := eq586950 X0
       grind)
    | (have r₁ := eq28 (M.op x y) y
       have r₂ := eq586950 X0
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq586950 X0
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq586950 X0
       grind)
    | exact resolve eq28 eq586950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq586950
  have eq587372 : ∀ X0 : G, (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq587275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587275
  have eq587464 : ∀ X0 : G, (M.op x y) = (k (M.op x y) y) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6253 eq587372
    | (have j0 := eq587372 X0
       grind)
    | exact resolve eq587372 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587372
  have eq587483 : ∀ X0 : G, (M.op x y) = (k (M.op x y) y) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq587464 X0
       grind)
    | (have r₁ := eq587464 X0
       have r₂ := eq6389
       grind)
    | exact resolve eq587464 eq6389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389 eq587464
  have eq587516 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1075 X0 x
       have i₂ := eq587483 (k X0 x)
       grind)
    | exact superpose eq587483 eq1075
    | (have j1 := eq587483 X0
       grind)
    | exact resolve eq1075 eq587483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587483
  have eq587526 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq587516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587516
  have eq587537 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq587526 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq587526
    | (have j0 := eq587526 X0
       grind)
    | exact resolve eq587526 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587526
  have eq587559 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq587537
    | (have j0 := eq587537 X0
       grind)
    | exact resolve eq587537 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587537
  have eq587575 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6303 eq587559
    | (have j0 := eq587559 X0
       grind)
    | exact resolve eq587559 eq6303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587559
  have eq587580 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq587575
    | (have j0 := eq587575 X0
       grind)
    | exact resolve eq587575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587575
  have eq587596 : ∀ X0 : G, (τ (σ X0)) = (k y X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq587580 eq48
    | exact resolve eq48 eq587580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq587580
  have eq588482 : ∀ X0 : G, (k y X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq587596 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq587596
    | exact resolve eq587596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587596
  have eq589595 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) y)) = (k X3 (M.op (M.op (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2309 y X1 X2 X3 x
       have i₂ := eq588482 (M.op (k X2 (M.op (M.op (M.op X3 x) X3) x)) X2)
       grind)
    | exact superpose eq588482 eq2309
    | exact resolve eq2309 eq588482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq588482
  have eq590127 : ∀ X3 : G, (k X3 y) = (M.op X3 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X3
    first
    | (have i₁ := eq589595 x x x X3
       have i₂ := eq2174 x x x y
       grind)
    | exact superpose eq2174 eq589595
    | exact resolve eq589595 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq589595
  have eq610112 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6253
       have i₂ := eq590127 sF0
       grind)
    | exact superpose eq590127 eq6253
    | exact resolve eq6253 eq590127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590127
  have eq611897 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq610112 eq1075
    | exact resolve eq1075 eq610112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq610112
  have eq611908 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq611897
  have eq611916 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq611908
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq611908
    | exact resolve eq611908 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611908
  have eq611932 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq611916
    | exact resolve eq611916 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq611916
  have eq611947 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6303 eq611932
    | exact resolve eq611932 eq6303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611932
  have eq611958 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq611947
    | exact resolve eq611947 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq611947
  have eq611959 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq611958
  have eq611964 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq611959 eq176
    | exact resolve eq176 eq611959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq611984 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq611959 eq719
    | (have r₁ := eq719
       have r₂ := eq611959
       grind)
    | exact resolve eq719 eq611959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq612201 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq611959
  have eq612202 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq611984
  have eq612232 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq612202 eq611964
    | exact resolve eq611964 eq612202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611964
  have eq612575 : ∀ X0 : G, (M.op (τ (M.op (M.op (k (σ y) (σ x)) (σ y)) (σ x))) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq612202 eq17950
    | exact resolve eq17950 eq612202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17950 eq612202
  have eq612708 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq612232 eq612575
    | exact resolve eq612575 eq612232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612232 eq612575
  have eq612760 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq612708
    | exact resolve eq612708 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq612708
  have eq612796 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq612760 X0
       have i₂ := eq6245
       grind)
    | exact superpose eq6245 eq612760
    | exact resolve eq612760 eq6245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6245 eq612760
  have eq614689 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq612796 eq6253
    | exact resolve eq6253 eq612796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6253 eq612796
  have eq615720 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq614689 eq27
    | exact resolve eq27 eq614689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614689
  have eq615984 : y = (M.op x y) := by
    first
    | (have r₁ := eq615720
       have r₂ := eq5121
       grind)
    | exact resolve eq615720 eq5121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121 eq615720
  have eq615987 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq615984
       grind)
    | exact superpose eq615984 eq24
    | exact resolve eq24 eq615984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq615984
  have eq616398 : (σ x) = (σ y) := by
    first
    | exact superpose eq6254 eq615987
    | exact resolve eq615987 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254 eq615987
  have eq616982 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq616398 eq612201
    | (have r₁ := eq612201
       have r₂ := eq616398
       grind)
    | exact resolve eq612201 eq616398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612201 eq616398
  have eq616985 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq616982
  have eq617379 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq616985 eq27
    | exact resolve eq27 eq616985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq616985
  have eq617856 : False := by grind
  exact eq617856

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq28 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq47 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq48 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq58 X1 X0
       have r₂ := eq49 X0 X1
       grind)
    | (have r₁ := eq58 X0 (M.op X1 X1)
       have r₂ := eq49 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq58 X1 X1
       have r₂ := eq49 (k X1 X1) X1
       grind)
    | exact resolve eq58 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq58
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq63
  have eq192 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq198 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq192 X0 X1
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq192 X0 X0
       have r₂ := eq66 X0 X0
       grind)
    | exact resolve eq192 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq192
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq198 (σ X0) (σ X1)
       grind)
    | exact superpose eq198 eq15
    | exact resolve eq15 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq198 X0 X1
       grind)
    | exact superpose eq198 eq484
    | exact resolve eq484 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq484
  have eq493 : False := by grind
  exact eq493

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq207 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq210 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq207 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq207 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq207 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq207 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq2360 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq210
  have eq2416 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2360 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq636595 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2416 (σ X0) (σ X1)
       grind)
    | exact superpose eq2416 eq15
    | exact resolve eq15 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636617 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq636595 X0 X1
       have i₂ := eq2416 X0 X1
       grind)
    | exact superpose eq2416 eq636595
    | exact resolve eq636595 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416 eq636595
  have eq636653 : False := by grind
  exact eq636653

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pyx_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 x)
       have i₂ := eq14 X0 X0 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq10
    | exact resolve eq10 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq80 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq50
    | exact resolve eq50 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq81 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq80
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq79
    | exact resolve eq79 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq78
    | exact resolve eq78 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq90 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq76 sF3
       grind)
    | exact superpose eq76 eq74
    | exact resolve eq74 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq91 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq90
    | exact resolve eq90 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq90
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq56
    | exact resolve eq56 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq18147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq18148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq18147
    | exact resolve eq18147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq18159 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq18148
       have r₂ := eq28
       grind)
    | exact resolve eq18148 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148
  have eq18163 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq18159 eq116
    | exact resolve eq116 eq18159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq18159
  have eq18216 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq18163
    | exact resolve eq18163 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18163
  have eq18217 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18216
  have eq18228 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq18217
       grind)
    | exact superpose eq18217 eq56
    | exact resolve eq56 eq18217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq18235 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq433 y X0
       have i₂ := eq18217
       grind)
    | exact superpose eq18217 eq433
    | exact resolve eq433 eq18217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq18217
  have eq18267 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18235 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18235
    | (have j0 := eq18235 X0
       grind)
    | exact resolve eq18235 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18235
  have eq18512 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18228 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18228
    | (have j0 := eq18228 x
       grind)
    | exact resolve eq18228 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18228
  have eq18665 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq82
       have i₂ := eq18512
       grind)
    | exact superpose eq18512 eq82
    | exact resolve eq82 eq18512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq18512
  have eq18713 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq18665
    | exact resolve eq18665 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18665
  have eq19669 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq18267
    | (have j0 := eq18267 (σ x)
       grind)
    | exact resolve eq18267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18267
  have eq19806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19669 eq18713
    | exact resolve eq18713 eq19669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18713 eq19669
  have eq19840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19806
  have eq19846 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19840
       have r₂ := eq28
       grind)
    | exact resolve eq19840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19840
  have eq19987 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq19846 eq30
    | exact resolve eq30 eq19846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19846
  have eq20097 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq19987
    | exact resolve eq19987 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19987
  have eq20098 : x = y := by grind
  clear eq20097
  have eq20113 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20098
       grind)
    | exact superpose eq20098 eq19
    | exact resolve eq19 eq20098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20114 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20098
       grind)
    | exact superpose eq20098 eq25
    | exact resolve eq25 eq20098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20098
  have eq20215 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20114
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20114
    | exact resolve eq20114 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20114
  have eq20230 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20215 eq27
    | exact resolve eq27 eq20215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20215
  have eq20703 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20230 eq81
    | exact resolve eq81 eq20230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq20230
  have eq20752 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20703
       have i₂ := eq20113
       grind)
    | exact superpose eq20113 eq20703
    | exact resolve eq20703 eq20113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113 eq20703
  have eq20759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20752 eq15
    | exact resolve eq15 eq20752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20752
  have eq20813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20759
    | exact resolve eq20759 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20759
  have eq20824 : False := by grind
  exact eq20824
