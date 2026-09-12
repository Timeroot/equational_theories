import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_pxx_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq578 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq561
    | (have j0 := eq561 X0 X1
       grind)
    | exact resolve eq561 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq3117 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq578
    | exact resolve eq578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq3162 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3117 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3117
    | (have j0 := eq3117 X0 X1
       grind)
    | exact resolve eq3117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3117
  have eq3187 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3162 X0 X1
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq3162 X1 X0
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq3162 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq3162 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq3162
  have eq3202 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3187 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3187
    | exact resolve eq3187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3227 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3187 (σ X1) X0
       grind)
    | exact superpose eq3187 eq15
    | (have j1 := eq3187 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq3187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3281 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq3202 (τ X0) X1
       grind)
    | exact superpose eq3202 eq19
    | (have j1 := eq3202 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq3202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3202
  have eq3613 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3281 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3281
    | exact resolve eq3281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3668 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3613 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3613
    | (have j0 := eq3613 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq3613 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613
  have eq4774 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3227 x y
       grind)
    | exact superpose eq3227 eq16
    | (have j1 := eq3227 x y
       grind)
    | exact resolve eq16 eq3227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq4805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4774
       have i₂ := eq3668 x y
       grind)
    | exact superpose eq3668 eq4774
    | (have j1 := eq3668 (σ x) (σ y)
       grind)
    | (have r₁ := eq4774
       have r₂ := eq3668 x y
       grind)
    | (have r₁ := eq4774
       have r₂ := eq3668 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4774
       have r₂ := eq3668 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4774 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668 eq4774
  have eq4806 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq4805
  have eq4809 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4806
       grind)
    | exact superpose eq4806 eq16
    | exact resolve eq16 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq4810 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4809
       have r₂ := eq82 x
       grind)
    | exact resolve eq4809 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq4811 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4810
       grind)
    | exact superpose eq4810 eq16
    | exact resolve eq16 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4812 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4810
       grind)
    | exact superpose eq4810 eq10
    | exact resolve eq10 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq4863 : x = y := by
    first
    | (have i₁ := eq4812
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4812
    | exact resolve eq4812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4812
  have eq4864 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4811
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq4811
    | exact resolve eq4811 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq4811
  have eq4865 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4864
       have i₂ := eq4863
       grind)
    | exact superpose eq4863 eq4864
    | exact resolve eq4864 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863 eq4864
  have eq4866 : False := by grind
  exact eq4866

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pyx_pxx_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq299 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq299 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq301 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq296 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq296 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq296 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq301 (σ X0)
       grind)
    | exact superpose eq301 eq15
    | exact resolve eq15 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq315
    | exact resolve eq315 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq315
  have eq383 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq63
    | exact resolve eq63 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq300 (τ X0) X1
       grind)
    | exact superpose eq300 eq19
    | (have j1 := eq300 (τ X0) X1
       grind)
    | exact resolve eq19 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq467 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq300 (σ X0) (σ X1)
       grind)
    | exact superpose eq300 eq15
    | (have j1 := eq300 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq490 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq334 X1
       grind)
    | exact superpose eq334 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq467
  have eq708 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq464 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq464
    | exact resolve eq464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq762 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq1299 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq490 x y
       grind)
    | exact superpose eq490 eq16
    | (have j1 := eq490 x y
       grind)
    | exact resolve eq16 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1299
       have i₂ := eq762 x y
       grind)
    | exact superpose eq762 eq1299
    | (have j1 := eq762 x y
       grind)
    | (have r₁ := eq1299
       have r₂ := eq762 x y
       grind)
    | exact resolve eq1299 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq1299
  have eq1392 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1391
  have eq1396 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq63
    | exact resolve eq63 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq383 y
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq383
    | exact resolve eq383 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1425 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1400
       grind)
    | exact superpose eq1400 eq16
    | exact resolve eq16 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1449 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1425
       have i₂ := eq1396
       grind)
    | exact superpose eq1396 eq1425
    | exact resolve eq1425 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396 eq1425
  have eq1452 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1449
  have eq1453 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1452
  have eq1460 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq383 y
       have i₂ := eq1453
       grind)
    | exact superpose eq1453 eq383
    | exact resolve eq383 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq1461 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1453
       grind)
    | exact superpose eq1453 eq10
    | exact resolve eq10 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq1506 : x = (M.op y y) := by
    first
    | (have i₁ := eq1461
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1461
    | exact resolve eq1461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1509 : y = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1506
       grind)
    | exact superpose eq1506 eq63
    | exact resolve eq63 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1506
  have eq1540 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1460
       grind)
    | exact superpose eq1460 eq16
    | exact resolve eq16 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1551 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1540
       have i₂ := eq1509
       grind)
    | exact superpose eq1509 eq1540
    | exact resolve eq1540 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq1540
  have eq1552 : False := by grind
  exact eq1552

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq70 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq15
    | exact resolve eq15 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq78
    | exact resolve eq78 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq78
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq104
    | exact resolve eq104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq106
  have eq210 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq212 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq215 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq612 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq215 x y
       grind)
    | exact superpose eq215 eq16
    | (have j1 := eq215 x y
       grind)
    | exact resolve eq16 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1413 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq212
    | exact resolve eq212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq1488 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1413
    | (have j0 := eq1413 X0 X1
       grind)
    | exact resolve eq1413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq5718 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq612
       have i₂ := eq1488 y x
       grind)
    | exact superpose eq1488 eq612
    | (have j1 := eq1488 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq612
       have r₂ := eq1488 y x
       grind)
    | (have r₁ := eq612
       have r₂ := eq1488 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq612
       have r₂ := eq1488 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq612 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq1488
  have eq5719 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5718
  have eq5721 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5719
       grind)
    | exact superpose eq5719 eq16
    | exact resolve eq16 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719
  have eq5722 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5721
       have r₂ := eq85 x
       grind)
    | exact resolve eq5721 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5721
  have eq5730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109 x
       have i₂ := eq5722
       grind)
    | exact superpose eq5722 eq109
    | exact resolve eq109 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5722
  have eq5756 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5730
       have r₂ := eq16
       grind)
    | exact resolve eq5730 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5730
  have eq5759 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq10
    | exact resolve eq10 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5817 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5759
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5759
    | exact resolve eq5759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5759
  have eq5820 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5817
       grind)
    | exact superpose eq5817 eq16
    | exact resolve eq16 eq5817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5817
  have eq5821 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5820
       have r₂ := eq85 x
       grind)
    | exact resolve eq5820 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5820
  have eq5833 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5821
       grind)
    | exact superpose eq5821 eq10
    | exact resolve eq10 eq5821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5821
  have eq5891 : y = (M.op x x) := by
    first
    | (have i₁ := eq5833
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5833
    | exact resolve eq5833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5833
  have eq5903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109 x
       have i₂ := eq5891
       grind)
    | exact superpose eq5891 eq109
    | exact resolve eq109 eq5891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq5891
  have eq5928 : False := by grind
  exact eq5928

/-- `Equation2497`: `x = (y ◇ ((x ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation2497 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2497 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X0 X0) X0))
       have r₂ := eq9 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq64 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq66
    | exact resolve eq66 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq19
    | (have j1 := eq66 (τ X0)
       grind)
    | exact resolve eq19 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73
    | (have j0 := eq73 X0
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq83 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq77
    | (have j0 := eq77 X0
       grind)
    | exact resolve eq77 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq88 : ∀ X0 : G, (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq91 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0)))
       have i₂ := eq88 (τ X0)
       grind)
    | exact superpose eq88 eq18
    | exact resolve eq18 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq92 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq103 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (M.op (τ X0) X1) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ (k X0 X0)) X1)) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | (have j1 := eq67 X0
       grind)
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq548 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq11
    | (have j1 := eq83 X0
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq549 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq548 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq647 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq549 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq549
    | (have j0 := eq549 X0
       have j1 := eq66 X0
       grind)
    | exact resolve eq549 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 (τ (σ X0)))) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0) X1
       have i₂ := eq549 (σ X0)
       grind)
    | exact superpose eq549 eq34
    | (have j1 := eq549 (σ X0)
       grind)
    | exact resolve eq34 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k (τ X0) (τ X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq549 (τ X0)
       grind)
    | exact superpose eq549 eq18
    | (have j1 := eq549 (τ X0)
       grind)
    | exact resolve eq18 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq549
  have eq670 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq665 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq665
    | (have j0 := eq665 X0
       grind)
    | exact resolve eq665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq675 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq687 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq647 X0
       have j1 := eq75 X0
       grind)
    | (have r₁ := eq647 X0
       have r₂ := eq75 X0
       grind)
    | exact resolve eq647 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq690 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq670 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq670
    | (have j0 := eq670 X0
       grind)
    | exact resolve eq670 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq694 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq708 : ∀ X0 X1 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k (τ X1) X0) = (k (τ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq717 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq766 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1321 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq690 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq690
    | (have j0 := eq690 X0
       have j1 := eq66 X0
       grind)
    | exact resolve eq690 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1361 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have j0 := eq1321 X0
       have j1 := eq75 X0
       grind)
    | (have r₁ := eq1321 X0
       have r₂ := eq75 X0
       grind)
    | exact resolve eq1321 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1321
  have eq1557 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ (τ (σ X0))) (τ (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq1361 (σ X0)
       grind)
    | exact superpose eq1361 eq29
    | (have j1 := eq1361 (σ X0)
       grind)
    | exact resolve eq29 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1565 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ (τ (σ X0))) (τ (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq1557 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1557
    | (have j0 := eq1557 X0
       grind)
    | exact resolve eq1557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1582 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1565 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1565
    | (have j0 := eq1565 X0
       grind)
    | exact resolve eq1565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1783 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (σ (M.op (τ X0) (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq1582 X0
       grind)
    | exact superpose eq1582 eq11
    | (have j1 := eq1582 X0
       grind)
    | exact resolve eq11 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582
  have eq2382 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq65
  have eq2393 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2413 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq2393 (τ X0)
       grind)
    | exact superpose eq2393 eq92
    | (have j1 := eq2393 (τ X0)
       grind)
    | exact resolve eq92 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2415 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq2393 X0
       grind)
    | exact superpose eq2393 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq2393 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq2393 X0
       grind)
    | exact resolve eq12 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq2416 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2415 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2419 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2413 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq2413
    | (have j0 := eq2413 X0
       grind)
    | exact resolve eq2413 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2718 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1783 X0
       have i₂ := eq687 X0
       grind)
    | exact superpose eq687 eq1783
    | (have j0 := eq1783 X0
       have j1 := eq687 X0
       grind)
    | exact resolve eq1783 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq1783
  have eq2750 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq4385 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq12
    | (have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq12 X1 (τ X0)
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq103 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4386 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4385 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385
  have eq6826 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq766 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq766
    | (have j0 := eq766 (τ X0) (τ X1)
       grind)
    | exact resolve eq766 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6841 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6826 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6826
    | (have j0 := eq6826 X0 X1
       grind)
    | exact resolve eq6826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6826
  have eq6845 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6841 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6841
    | (have j0 := eq6841 X0 X1
       grind)
    | exact resolve eq6841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841
  have eq6848 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6845 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6845
    | (have j0 := eq6845 X0 X1
       grind)
    | exact resolve eq6845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq6849 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6848 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6848
    | (have j0 := eq6848 X0 X1
       grind)
    | exact resolve eq6848 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6848
  have eq6850 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6849 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6849
    | (have j0 := eq6849 X0 X1
       grind)
    | exact resolve eq6849 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6849
  have eq6851 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6850 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6850
    | (have j0 := eq6850 X0 X1
       grind)
    | exact resolve eq6850 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6850
  have eq14072 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (M.op (k (σ (τ X0)) X0) X1)) X1) ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq514 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq514
    | exact resolve eq514 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq14118 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (k X0 X0) X1)) X1) = X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14072 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14072
    | (have j0 := eq14072 X0 X1
       grind)
    | exact resolve eq14072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14072
  have eq14133 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (k X0 X0) X1)) X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14118 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14118
    | (have j0 := eq14118 X0 X1
       grind)
    | exact resolve eq14118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14118
  have eq14180 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (k X0 X0) x
       have i₂ := eq14133 X0 x
       grind)
    | exact superpose eq14133 eq63
    | (have j0 := eq63 (k X0 X0) x
       have j1 := eq14133 X0 x
       grind)
    | exact resolve eq63 eq14133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq14183 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14180
  have eq14303 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4386 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4386
    | exact resolve eq4386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq14378 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14303 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14303
    | (have j0 := eq14303 X0 X1
       grind)
    | exact resolve eq14303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14303
  have eq14418 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq14378 X0 X1
       grind)
    | exact superpose eq14378 eq10
    | (have j1 := eq14378 X0 X1
       grind)
    | exact resolve eq10 eq14378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14479 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14418 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq14418
    | (have j0 := eq14418 X0 X1
       grind)
    | exact resolve eq14418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14418
  have eq14481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14479 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14479
    | (have j0 := eq14479 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq14479 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14502 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14479 (σ X0) X1
       grind)
    | exact superpose eq14479 eq23
    | (have j1 := eq14479 (σ X0) X1
       grind)
    | exact resolve eq23 eq14479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14563 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19713 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (k X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq717
    | (have j0 := eq717 X1 X1
       grind)
    | exact resolve eq717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq19885 : ∀ X0 X1 X2 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (k X2 X0) = (k X2 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (k X0 X0)
       have i₂ := eq19713 X2 X0
       grind)
    | exact superpose eq19713 eq23
    | (have j1 := eq19713 X2 X0
       grind)
    | exact resolve eq23 eq19713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19713
  have eq19932 : ∀ X0 X1 X2 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (k X2 X0) = (k X2 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19885 X0 X1 X2
       have i₂ := eq23 X1 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq19885
    | (have j0 := eq19885 X0 X1 X2
       grind)
    | exact resolve eq19885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19885
  have eq20312 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2419 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2419
    | exact resolve eq2419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq20389 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq20312 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq20312
    | (have j0 := eq20312 X0
       grind)
    | exact resolve eq20312 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312
  have eq20398 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq20389 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20389
    | (have j0 := eq20389 X0
       grind)
    | exact resolve eq20389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20389
  have eq20404 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq20398 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq20398
    | (have j0 := eq20398 X0
       grind)
    | exact resolve eq20398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20398
  have eq26758 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14502 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14502
    | exact resolve eq14502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14502
  have eq26891 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26758 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq26758
    | (have j0 := eq26758 X0 X1
       grind)
    | exact resolve eq26758 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26758
  have eq26894 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26891 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq26891
    | (have j0 := eq26891 (τ (σ (k X0 X1))) (τ (M.op (σ X1) (σ X0)))
       grind)
    | exact resolve eq26891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26891
  have eq27092 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26894 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq26894
    | (have j0 := eq26894 X0 X1
       grind)
    | exact resolve eq26894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26894
  have eq118580 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14481 y x
       grind)
    | exact superpose eq14481 eq16
    | (have j1 := eq14481 x y
       grind)
    | exact resolve eq16 eq14481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14481
  have eq121718 : ∀ X0 X1 X2 : G, (k X2 X1) = (k X2 (k X1 X1)) ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19932 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19932
    | (have j0 := eq19932 X1 X1 X2
       grind)
    | exact resolve eq19932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19932
  have eq122355 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121718 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121718
  have eq122509 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq122355 X0 X0
       have i₂ := eq2416 X0
       grind)
    | exact superpose eq2416 eq122355
    | (have j1 := eq2416 X0
       grind)
    | exact resolve eq122355 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122355
  have eq122628 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq122509 X0
       have j1 := eq66 X0
       grind)
    | (have r₁ := eq122509 X0
       have r₂ := eq66 X0
       grind)
    | exact resolve eq122509 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq122509
  have eq123044 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (σ X0) (σ X0)
       have i₂ := eq122628 (σ X0)
       grind)
    | exact superpose eq122628 eq34
    | (have j1 := eq122628 (σ X0)
       grind)
    | exact resolve eq34 eq122628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq122628
  have eq123154 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq123044 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123044
    | (have j0 := eq123044 X0
       grind)
    | exact resolve eq123044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123044
  have eq123200 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq123154 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq123154
    | (have j0 := eq123154 X0
       grind)
    | exact resolve eq123154 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123154
  have eq192352 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq27092 X0 X1
       grind)
    | exact superpose eq27092 eq10
    | (have j1 := eq27092 X0 X1
       grind)
    | exact resolve eq10 eq27092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27092
  have eq192526 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq192352 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq192352
    | (have j0 := eq192352 X0 X1
       grind)
    | exact resolve eq192352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192352
  have eq192974 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192526 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192526
    | (have j0 := eq192526 X1 (τ X0)
       grind)
    | exact resolve eq192526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq192526 X0 X1
       grind)
    | exact superpose eq192526 eq11
    | (have j1 := eq192526 X0 X1
       grind)
    | exact resolve eq11 eq192526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192526
  have eq193602 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192974 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192974
    | (have j0 := eq192974 X1 (τ X0)
       grind)
    | exact resolve eq192974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193746 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq192974 X1 X0
       grind)
    | exact superpose eq192974 eq11
    | (have j1 := eq192974 X1 X0
       grind)
    | exact resolve eq11 eq192974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192974
  have eq194005 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq193746 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq193746
    | (have j0 := eq193746 X0 X1
       grind)
    | exact resolve eq193746 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq193746
  have eq194042 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193602 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq193602
    | (have j0 := eq193602 X0 X1
       grind)
    | exact resolve eq193602 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193602
  have eq194050 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq194042 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq194042
    | (have j0 := eq194042 X0 X1
       grind)
    | exact resolve eq194042 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194042
  have eq194704 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ X1))) ∨ (σ (σ X0)) = X1 ∨ (k (σ (σ X0)) X1) = (M.op X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ X1)
       have i₂ := eq194005 (σ X0) X1
       grind)
    | exact superpose eq194005 eq29
    | (have j1 := eq194005 (σ X0) X1
       grind)
    | exact resolve eq29 eq194005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194005
  have eq194808 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = X0 ∨ (σ (σ X0)) = X1 ∨ (k (σ (σ X0)) X1) = (M.op X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq194704 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq194704
    | (have j0 := eq194704 X0 X1
       grind)
    | exact resolve eq194704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194704
  have eq195809 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq194050 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194050
  have eq196020 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 (τ X1))) ∨ (τ X1) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq195809 X0 (τ X1)
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq195809
    | (have j0 := eq195809 X0 (τ X1)
       have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq195809 X0 X1
       have r₂ := eq103 X0 (τ (M.op X1 X0))
       grind)
    | (have r₁ := eq195809 X0 X1
       have r₂ := eq103 (M.op X1 X0) (τ X0)
       grind)
    | exact resolve eq195809 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq195809
  have eq196078 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196020
  have eq196079 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (τ X0) = (τ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq196078 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196078
  have eq196443 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193235 y x
       grind)
    | exact superpose eq193235 eq16
    | (have j1 := eq193235 x y
       grind)
    | exact resolve eq16 eq193235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193235
  have eq196568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq196443
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq196443
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq196443
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq196443
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq196443 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq196443
       have i₂ := eq14378 x y
       grind)
    | exact superpose eq14378 eq196443
    | (have j1 := eq14378 x y
       grind)
    | (have r₁ := eq196443
       have r₂ := eq14378 x y
       grind)
    | (have r₁ := eq196443
       have r₂ := eq14378 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq196443
       have r₂ := eq14378 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq196443 eq14378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14378 eq196443
  have eq196574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq196571
  have eq196575 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq196574
  have eq196578 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq196568
  have eq196579 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq196578
  have eq196581 : y = (k y x) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq196575
       grind)
    | exact superpose eq196575 eq16
    | exact resolve eq16 eq196575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196575
  have eq196582 : y = (M.op x y) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq196579
       grind)
    | exact superpose eq196579 eq16
    | exact resolve eq16 eq196579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196579
  have eq196884 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq766 x y
       have i₂ := eq196581
       grind)
    | exact superpose eq196581 eq766
    | (have j0 := eq766 x y
       grind)
    | exact resolve eq766 eq196581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196581
  have eq196895 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq196884
  have eq196896 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq196895
  have eq306311 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq196079 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196079
    | (have j0 := eq196079 (τ (k X1 X0)) X1
       grind)
    | exact resolve eq196079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196079
  have eq306693 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq306311 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq306311
    | (have j0 := eq306311 X0 X1
       grind)
    | exact resolve eq306311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306311
  have eq597579 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (τ X1))) ∨ (σ (σ (τ X0))) = X1 ∨ (k (σ (σ (τ X0))) X1) = (M.op X1 (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (τ X1) X0
       have i₂ := eq194808 (τ X0) X1
       grind)
    | exact superpose eq194808 eq32
    | (have j1 := eq194808 (τ X0) X1
       grind)
    | exact resolve eq32 eq194808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq194808
  have eq597701 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (τ X0) = (τ (k X0 (τ X1))) ∨ (k (σ (σ (τ X0))) X1) = (M.op X1 (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq597579 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq597579
    | (have j0 := eq597579 X0 X1
       grind)
    | exact resolve eq597579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597579
  have eq597898 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (τ X1))) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq597701 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq597701
    | (have j0 := eq597701 X0 X1
       grind)
    | exact resolve eq597701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597701
  have eq598172 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597898 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq597898
    | (have j0 := eq597898 X0 (σ X1)
       grind)
    | exact resolve eq597898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597898
  have eq599077 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq598172 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq598172
    | (have j0 := eq598172 X0 X1
       grind)
    | exact resolve eq598172 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598172
  have eq600950 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq599077 x y
       grind)
    | exact superpose eq599077 eq16
    | (have j1 := eq599077 x y
       grind)
    | exact resolve eq16 eq599077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599077
  have eq601367 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq600950
       have i₂ := eq306693 x y
       grind)
    | exact superpose eq306693 eq600950
    | (have j1 := eq306693 x y
       grind)
    | (have r₁ := eq600950
       have r₂ := eq306693 x y
       grind)
    | (have r₁ := eq600950
       have r₂ := eq306693 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq600950
       have r₂ := eq306693 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq600950 eq306693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306693 eq600950
  have eq601374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq601367
  have eq601375 : x = y ∨ (σ x) = (σ y) ∨ (τ (k y x)) = (τ y) := by grind
  clear eq601374
  have eq601382 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq601375
       grind)
    | exact superpose eq601375 eq16
    | exact resolve eq16 eq601375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601375
  have eq602433 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (τ (k y x)) = (τ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq601382
       have i₂ := eq2750 x
       grind)
    | exact superpose eq2750 eq601382
    | (have j1 := eq2750 x
       grind)
    | (have r₁ := eq601382
       have r₂ := eq2750 x
       grind)
    | exact resolve eq601382 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601382
  have eq602502 : (σ x) = (σ y) ∨ (τ (k y x)) = (τ y) ∨ x = (k x x) := by grind
  clear eq602433
  have eq602518 : y = (τ (σ x)) ∨ (τ (k y x)) = (τ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq602502
       grind)
    | exact superpose eq602502 eq10
    | exact resolve eq10 eq602502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602502
  have eq602832 : x = y ∨ (τ (k y x)) = (τ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq602518
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq602518
    | exact resolve eq602518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602518
  have eq602833 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ (k y x)) = (τ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq602832
       grind)
    | exact superpose eq602832 eq16
    | exact resolve eq16 eq602832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602832
  have eq602834 : (τ (k y x)) = (τ y) ∨ x = (k x x) := by
    first
    | (have j1 := eq2750 x
       grind)
    | (have r₁ := eq602833
       have r₂ := eq2750 x
       grind)
    | exact resolve eq602833 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750 eq602833
  have eq602856 : (k y x) = (σ (τ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq602834
       grind)
    | exact superpose eq602834 eq11
    | exact resolve eq11 eq602834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602834
  have eq603276 : y = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq602856
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq602856
    | exact resolve eq602856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602856
  have eq605394 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq766 x y
       have i₂ := eq603276
       grind)
    | exact superpose eq603276 eq766
    | (have j0 := eq766 x y
       grind)
    | exact resolve eq766 eq603276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq605399 : y ≠ y ∨ x = y ∨ y = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq6851 y x
       have i₂ := eq603276
       grind)
    | exact superpose eq603276 eq6851
    | (have j0 := eq6851 x y
       grind)
    | (have r₁ := eq6851 y x
       have r₂ := eq603276
       grind)
    | (have r₁ := eq6851 x x
       have r₂ := eq603276
       grind)
    | exact resolve eq6851 eq603276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6851
  have eq605405 : x = y ∨ y = (M.op x y) ∨ x = (k x x) := by grind
  clear eq605399
  have eq605407 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq605394
  have eq605421 : x = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq603276
       have i₂ := eq605405
       grind)
    | exact superpose eq605405 eq603276
    | exact resolve eq603276 eq605405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605405
  have eq605422 : y = (M.op x y) ∨ x = (k x x) := by grind
  clear eq605421
  have eq608153 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq605407
       grind)
    | exact superpose eq605407 eq16
    | exact resolve eq16 eq605407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605407
  have eq608202 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq608153
       have i₂ := eq605422
       grind)
    | exact superpose eq605422 eq608153
    | exact resolve eq608153 eq605422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605422 eq608153
  have eq608226 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq608202
  have eq608227 : (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq608226
  have eq608232 : y = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq608227
       grind)
    | exact superpose eq608227 eq10
    | exact resolve eq10 eq608227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608227
  have eq608552 : x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq608232
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq608232
    | exact resolve eq608232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608232
  have eq608558 : x = (k x x) ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq603276
       have i₂ := eq608552
       grind)
    | exact superpose eq608552 eq603276
    | exact resolve eq603276 eq608552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603276 eq608552
  have eq608561 : x = (k x x) := by grind
  clear eq608558
  have eq750105 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq196896
       grind)
    | exact superpose eq196896 eq16
    | exact resolve eq16 eq196896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196896
  have eq750171 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq750105
       have i₂ := eq196582
       grind)
    | exact superpose eq196582 eq750105
    | exact resolve eq750105 eq196582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196582 eq750105
  have eq750192 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq750171
  have eq750193 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq750192
  have eq750273 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq750295 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq750273
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq750273
    | exact resolve eq750273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750273
  have eq750338 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq750295
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq750295
    | exact resolve eq750295 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750295
  have eq750372 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by grind
  have eq750375 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by grind
  clear eq750372
  have eq750394 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq750375
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq750375
    | exact resolve eq750375 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750375
  have eq750404 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq750338
       have i₂ := eq750394
       grind)
    | exact superpose eq750394 eq750338
    | exact resolve eq750338 eq750394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750338 eq750394
  have eq750533 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq750404
  have eq750534 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq750533
  have eq750547 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 y
       have i₂ := eq750534
       grind)
    | exact superpose eq750534 eq23
    | exact resolve eq23 eq750534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750552 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq29 y X0
       have i₂ := eq750534
       grind)
    | exact superpose eq750534 eq29
    | exact resolve eq29 eq750534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750534
  have eq750874 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq750552 X0
       have i₂ := eq29 x X0
       grind)
    | exact superpose eq29 eq750552
    | exact resolve eq750552 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750552
  have eq750879 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq750547 X0
       have i₂ := eq23 X0 x
       grind)
    | exact superpose eq23 eq750547
    | exact resolve eq750547 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750547
  have eq750972 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k y X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq750874 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq750874
    | exact resolve eq750874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750874
  have eq751416 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq750193
       have i₂ := eq750972 X0
       grind)
    | exact superpose eq750972 eq750193
    | (have j1 := eq750972 X0
       grind)
    | exact resolve eq750193 eq750972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750972
  have eq751980 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq750879 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq750879
    | exact resolve eq750879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750879
  have eq752398 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k X0 y) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq750193
       have i₂ := eq751980 X0
       grind)
    | exact superpose eq751980 eq750193
    | (have j1 := eq751980 X0
       grind)
    | exact resolve eq750193 eq751980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751980
  have eq756805 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k y X0) = (k x X0) ∨ (M.op x x) = (k x x) := by
    intro X0
    grind
  have eq756808 : ∀ X0 : G, (σ x) = (σ y) ∨ (k y X0) = (k x X0) ∨ (M.op x x) = (k x x) := by
    intro X0
    first
    | (have j0 := eq756805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756805
  have eq756829 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (σ y) ∨ (k y X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq756808 X0
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq756808
    | (have j0 := eq756808 X0
       grind)
    | exact resolve eq756808 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756808
  have eq756840 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k y X0) = (k x X0) ∨ (σ x) = (σ y) ∨ (k x X1) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq751416 X0
       have i₂ := eq756829 X1
       grind)
    | exact superpose eq756829 eq751416
    | (have j0 := eq751416 X0
       have j1 := eq756829 X0
       grind)
    | exact resolve eq751416 eq756829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751416 eq756829
  have eq756968 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k y X0) = (k x X0) ∨ (k x X1) = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq756840 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756840
  have eq756969 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (k y X0) = (k x X0) ∨ (k x X1) = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq756968 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756968
  have eq757181 : ∀ X0 X1 X2 : G, (k y (τ X0)) = (τ (k (σ x) X0)) ∨ (k x X1) = (k y X1) ∨ (k x X2) = (k y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 y X0
       have i₂ := eq756969 X1 X2
       grind)
    | exact superpose eq756969 eq29
    | (have j1 := eq756969 X1 X1
       grind)
    | exact resolve eq29 eq756969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756969
  have eq757505 : ∀ X0 X1 X2 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (k x X1) = (k y X1) ∨ (k x X2) = (k y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757181 X0 X1 X2
       have i₂ := eq29 x X0
       grind)
    | exact superpose eq29 eq757181
    | (have j0 := eq757181 X0 (τ X0) (τ X0)
       grind)
    | exact resolve eq757181 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq757181
  have eq918605 : ∀ X0 X1 : G, (k x (τ X0)) ≠ (k x (τ X0)) ∨ (k x X1) = (k y X1) ∨ (k y (τ X0)) = (k x (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq757505 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757505
  have eq918606 : ∀ X0 X1 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (k x X1) = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq918605 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918605
  have eq919080 : ∀ X0 : G, (k x (τ X0)) ≠ (k x (τ X0)) ∨ (k y (τ X0)) = (k x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq918606 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918606
  have eq919081 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq919080 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919080
  have eq919215 : ∀ X0 : G, (k y X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq919081 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq919081
    | exact resolve eq919081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919081
  have eq919998 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq118580
       have i₂ := eq919215 x
       grind)
    | exact superpose eq919215 eq118580
    | exact resolve eq118580 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118580
  have eq920236 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (k x y) X0)) X0) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq14133 y x
       have i₂ := eq919215 y
       grind)
    | exact superpose eq919215 eq14133
    | exact resolve eq14133 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14133
  have eq920481 : y = (k y (k x y)) ∨ (M.op (σ y) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq123200 y
       have i₂ := eq919215 y
       grind)
    | exact superpose eq919215 eq123200
    | exact resolve eq123200 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123200
  have eq920807 : ∀ X0 : G, y = (M.op X0 y) ∨ y = X0 ∨ (k x X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq919215 X0
       grind)
    | exact superpose eq919215 eq14
    | (have j0 := eq14 y X0
       grind)
    | exact resolve eq14 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920823 : ∀ X0 : G, y = (k x X0) ∨ y = X0 ∨ (k x X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14479 X0 y
       have i₂ := eq919215 X0
       grind)
    | exact superpose eq919215 eq14479
    | (have j0 := eq14479 y (k x X0)
       grind)
    | exact resolve eq14479 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14479
  have eq920908 : y = (k x (M.op y y)) ∨ (M.op y y) = (k y y) := by
    first
    | (have i₁ := eq2416 y
       have i₂ := eq919215 (M.op y y)
       grind)
    | exact superpose eq919215 eq2416
    | (have j0 := eq2416 y
       grind)
    | exact resolve eq2416 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq921199 : (M.op y y) = (k x y) ∨ y = (k x (M.op y y)) := by
    first
    | (have i₁ := eq920908
       have i₂ := eq919215 y
       grind)
    | exact superpose eq919215 eq920908
    | exact resolve eq920908 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920908
  have eq921348 : y = (k x (k x y)) ∨ (M.op (σ y) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq920481
       have i₂ := eq919215 (k x y)
       grind)
    | exact superpose eq919215 eq920481
    | exact resolve eq920481 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920481
  have eq921437 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq919998
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq919998
    | exact resolve eq919998 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919998
  have eq921800 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq921437
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq921437
    | exact resolve eq921437 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921437
  have eq921801 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq921800
  have eq978769 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq920823 x
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq920823
    | (have j0 := eq920823 x
       grind)
    | exact resolve eq920823 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980240 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = X0 ∨ (k x X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq920823 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920823
  have eq980708 : x = (M.op x y) ∨ x = y := by grind
  clear eq978769
  have eq980724 : ∀ X0 : G, (k x X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq980240 X0
       have j1 := eq920807 X0
       grind)
    | (have r₁ := eq980240 X0
       have r₂ := eq920807 X0
       grind)
    | (have r₁ := eq980240 X0
       have r₂ := eq920807 (M.op X0 y)
       grind)
    | exact resolve eq980240 eq920807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920807 eq980240
  have eq981710 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq921801
       have i₂ := eq980708
       grind)
    | exact superpose eq980708 eq921801
    | exact resolve eq921801 eq980708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921801 eq980708
  have eq981760 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq981710
  have eq1085765 : y = (k x (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (k x (M.op y y)) := by
    first
    | (have i₁ := eq921348
       have i₂ := eq921199
       grind)
    | exact superpose eq921199 eq921348
    | exact resolve eq921348 eq921199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921199 eq921348
  have eq1085889 : y = (k x (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1085765
  have eq1105549 : x = (k x (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1085889
       have i₂ := eq981760
       grind)
    | exact superpose eq981760 eq1085889
    | exact resolve eq1085889 eq981760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085889
  have eq1105702 : x = (k x (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1105549
       have r₂ := eq750193
       grind)
    | exact resolve eq1105549 eq750193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750193 eq1105549
  have eq1105788 : x = (M.op (M.op x x) y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq980724 (M.op x x)
       have i₂ := eq1105702
       grind)
    | exact superpose eq1105702 eq980724
    | (have j0 := eq980724 (M.op x x)
       grind)
    | exact resolve eq980724 eq1105702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980724 eq1105702
  have eq1139423 : x ≠ y ∨ y = (M.op x x) ∨ y = (k y (M.op x x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14563 y (M.op x x)
       have i₂ := eq1105788
       grind)
    | exact superpose eq1105788 eq14563
    | (have j0 := eq14563 y (M.op x x)
       grind)
    | exact resolve eq14563 eq1105788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14563 eq1105788
  have eq1139442 : x ≠ y ∨ y = (M.op x x) ∨ y = (k y (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1139423
  have eq1139477 : y = (M.op x x) ∨ y = (k y (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1139442
       have r₂ := eq981760
       grind)
    | exact resolve eq1139442 eq981760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139442
  have eq1139480 : y = (k x (M.op x x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1139477
       have i₂ := eq919215 (M.op x x)
       grind)
    | exact superpose eq919215 eq1139477
    | exact resolve eq1139477 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139477
  have eq1140366 : (σ x) = (σ y) ∨ (M.op x x) = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20404 x
       have i₂ := eq1139480
       grind)
    | exact superpose eq1139480 eq20404
    | (have j0 := eq20404 x
       grind)
    | exact resolve eq20404 eq1139480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20404 eq1139480
  have eq1140441 : (σ x) = (σ y) ∨ (M.op x x) = (k x x) ∨ y = (M.op x x) := by grind
  clear eq1140366
  have eq1140492 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1140441
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1140441
    | exact resolve eq1140441 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140441
  have eq1140711 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq1140492
  have eq1140749 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1140711
       have r₂ := eq981760
       grind)
    | exact resolve eq1140711 eq981760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981760 eq1140711
  have eq1140811 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k X0 y) = (k X0 x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq752398 X0
       have i₂ := eq1140749
       grind)
    | exact superpose eq1140749 eq752398
    | (have j0 := eq752398 X0
       grind)
    | exact resolve eq752398 eq1140749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752398 eq1140749
  have eq1140999 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k X0 y) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1140811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140811
  have eq1141000 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 y) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1140999 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140999
  have eq1141023 : ∀ X0 X1 : G, (k (τ X0) y) = (τ (k X0 (σ x))) ∨ (k X1 x) = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 y
       have i₂ := eq1141000 X1
       grind)
    | exact superpose eq1141000 eq23
    | (have j1 := eq1141000 X1
       grind)
    | exact resolve eq23 eq1141000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141000
  have eq1141678 : ∀ X0 X1 : G, (k (τ X0) y) = (k (τ X0) x) ∨ (k X1 x) = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1141023 X0 X1
       have i₂ := eq23 X0 x
       grind)
    | exact superpose eq23 eq1141023
    | (have j0 := eq1141023 X0 (τ X0)
       grind)
    | exact resolve eq1141023 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1141023
  have eq1145254 : ∀ X0 : G, (k (τ X0) x) ≠ (k (τ X0) x) ∨ (k (τ X0) y) = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq1141678 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141678
  have eq1145255 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq1145254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145254
  have eq1145405 : ∀ X0 : G, (k X0 y) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1145255 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1145255
    | exact resolve eq1145255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145255
  have eq1146400 : (k (k y x) (k y x)) = (M.op (k y x) (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14183 y
       have i₂ := eq1145405 y
       grind)
    | exact superpose eq1145405 eq14183
    | exact resolve eq14183 eq1145405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14183
  have eq1147141 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (k x x) X0)) X0) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq920236 X0
       have i₂ := eq1145405 x
       grind)
    | exact superpose eq1145405 eq920236
    | exact resolve eq920236 eq1145405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920236 eq1145405
  have eq1147212 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x X0)) X0) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1147141 X0
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1147141
    | exact resolve eq1147141 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147141
  have eq1147875 : (k (k x x) (k x x)) = (M.op (k x x) (k x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1146400
       have i₂ := eq919215 x
       grind)
    | exact superpose eq919215 eq1146400
    | exact resolve eq1146400 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146400
  have eq1148467 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x X0)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1147212 X0
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1147212
    | (have j0 := eq1147212 X0
       grind)
    | exact resolve eq1147212 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147212
  have eq1149056 : (M.op x x) = (k x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1147875
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1147875
    | exact resolve eq1147875 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147875
  have eq1150002 : x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1149056
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1149056
    | exact resolve eq1149056 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149056
  have eq1150779 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1150002
       have i₂ := eq919215 x
       grind)
    | exact superpose eq919215 eq1150002
    | exact resolve eq1150002 eq919215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919215 eq1150002
  have eq1151214 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1150779
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1150779
    | exact resolve eq1150779 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150779
  have eq1195172 : y = (M.op (M.op x x) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1148467 x
       have i₂ := eq1151214
       grind)
    | exact superpose eq1151214 eq1148467
    | exact resolve eq1148467 eq1151214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148467
  have eq1195333 : y = (M.op (M.op x x) x) ∨ x = y := by grind
  clear eq1195172
  have eq1195492 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1195333
       have i₂ := eq1151214
       grind)
    | exact superpose eq1151214 eq1195333
    | exact resolve eq1195333 eq1151214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195333
  have eq1195584 : y = (M.op x x) ∨ x = y := by grind
  clear eq1195492
  have eq1195716 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1151214
       have i₂ := eq1195584
       grind)
    | exact superpose eq1195584 eq1151214
    | exact resolve eq1151214 eq1195584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151214 eq1195584
  have eq1195862 : x = y := by grind
  clear eq1195716
  have eq1196565 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1195862
       grind)
    | exact superpose eq1195862 eq16
    | exact resolve eq16 eq1195862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195862
  have eq1197086 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq1197108 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1197086
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1197086
    | exact resolve eq1197086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197086
  have eq1197163 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1197108
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1197108
    | exact resolve eq1197108 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197108
  have eq1334732 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by grind
  have eq1334735 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by grind
  clear eq1334732
  have eq1334787 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1334735
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1334735
    | exact resolve eq1334735 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334735
  have eq1334830 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1197163
       have i₂ := eq1334787
       grind)
    | exact superpose eq1334787 eq1197163
    | exact resolve eq1197163 eq1334787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197163 eq1334787
  have eq1334984 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1334830
  have eq1334985 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1334984
  have eq1335135 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1196565
       have i₂ := eq1334985
       grind)
    | exact superpose eq1334985 eq1196565
    | exact resolve eq1196565 eq1334985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196565 eq1334985
  have eq1335814 : (σ x) ≠ (σ x) ∨ (M.op x x) = (k x x) := by grind
  have eq1335817 : (M.op x x) = (k x x) := by grind
  clear eq1335814
  have eq1335869 : x = (M.op x x) := by
    first
    | (have i₁ := eq1335817
       have i₂ := eq608561
       grind)
    | exact superpose eq608561 eq1335817
    | exact resolve eq1335817 eq608561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608561 eq1335817
  have eq1335913 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1335135
       have i₂ := eq1335869
       grind)
    | exact superpose eq1335869 eq1335135
    | exact resolve eq1335135 eq1335869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335135 eq1335869
  have eq1336065 : False := by grind
  exact eq1336065

/-- `Equation2497`: `x = (y ◇ ((x ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation2497 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2497 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2497.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X1) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq106 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ (M.op X0 X0)) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq465 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq450
    | (have j0 := eq450 X0 X1
       grind)
    | exact resolve eq450 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq3919 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (M.op (M.op X0 X0) X2)) X2) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 X1 X2
       have i₂ := eq465 X0 X1
       grind)
    | exact superpose eq465 eq106
    | (have j1 := eq465 X0 X1
       grind)
    | exact resolve eq106 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq465
  have eq3965 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3919 X0 X1 x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq3919
    | (have j0 := eq3919 X0 X1 x
       grind)
    | exact resolve eq3919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq3966 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3965 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965
  have eq4008 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3966 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3966
    | exact resolve eq3966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966
  have eq4115 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4008 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq4008
    | (have j0 := eq4008 (τ (k X0 X1)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq4008 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4008
  have eq4143 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4115 X1 X0
       grind)
    | exact superpose eq4115 eq11
    | (have j1 := eq4115 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq4260 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4143 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4143
    | (have j0 := eq4143 (k X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq4143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq4286 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq4260 (τ X0) X1
       grind)
    | exact superpose eq4260 eq19
    | (have j1 := eq4260 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4306 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4260 (σ X0) (σ X1)
       grind)
    | exact superpose eq4260 eq15
    | (have j1 := eq4260 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq4523 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4286 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4286
    | exact resolve eq4286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286
  have eq4577 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4523 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4523
    | (have j0 := eq4523 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq4523 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq4930 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4306 x y
       grind)
    | exact superpose eq4306 eq16
    | (have j1 := eq4306 x y
       grind)
    | exact resolve eq16 eq4306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4306
  have eq4953 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4930
       have i₂ := eq4577 x y
       grind)
    | exact superpose eq4577 eq4930
    | (have j1 := eq4577 (σ x) (σ y)
       grind)
    | (have r₁ := eq4930
       have r₂ := eq4577 x y
       grind)
    | (have r₁ := eq4930
       have r₂ := eq4577 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4930
       have r₂ := eq4577 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4930 eq4577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577 eq4930
  have eq4956 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq4953
  have eq4959 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4956
       grind)
    | exact superpose eq4956 eq16
    | exact resolve eq16 eq4956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4960 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4959
       have r₂ := eq22 x
       grind)
    | exact resolve eq4959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4959
  have eq4961 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4960
       grind)
    | exact superpose eq4960 eq16
    | exact resolve eq16 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4962 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4960
       grind)
    | exact superpose eq4960 eq10
    | exact resolve eq10 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4960
  have eq5012 : x = y := by
    first
    | (have i₁ := eq4962
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4962
    | exact resolve eq4962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq5013 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4961
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq4961
    | exact resolve eq4961 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4961
  have eq5014 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5013
       have i₂ := eq5012
       grind)
    | exact superpose eq5012 eq5013
    | exact resolve eq5013 eq5012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5012 eq5013
  have eq5015 : False := by grind
  exact eq5015

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 x x
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
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
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
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq336 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq363 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq336
    | (have j0 := eq336 X0 X1
       grind)
    | exact resolve eq336 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq336
  have eq367 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq363 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq363 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq370 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq367
    | (have j0 := eq367 X0 X1
       grind)
    | exact resolve eq367 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq470 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq370 (σ X0) X1
       grind)
    | exact superpose eq370 eq15
    | (have j1 := eq370 (σ X0) X1
       grind)
    | exact resolve eq15 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq500 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq477
    | (have j0 := eq477 X0 X1
       grind)
    | exact resolve eq477 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq477
  have eq528 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq470 (τ X1) X0
       grind)
    | exact superpose eq470 eq17
    | (have j1 := eq470 (τ X1) X0
       grind)
    | exact resolve eq17 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq470
  have eq922 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq528
    | exact resolve eq528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq971 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq922
    | (have j0 := eq922 X0 X1
       grind)
    | exact resolve eq922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq3624 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq500 x y
       grind)
    | exact superpose eq500 eq16
    | (have j1 := eq500 x y
       grind)
    | exact resolve eq16 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3646 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq3708 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3624
       have i₂ := eq971 y x
       grind)
    | exact superpose eq971 eq3624
    | (have j1 := eq971 y x
       grind)
    | (have r₁ := eq3624
       have r₂ := eq971 y x
       grind)
    | exact resolve eq3624 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq3624
  have eq3709 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3708
  have eq3714 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3709
       grind)
    | exact superpose eq3709 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3709
       grind)
    | exact resolve eq13 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3719 : x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3714
  have eq3843 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3646 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq3646
    | (have j0 := eq3646 (τ X1) (τ X0)
       grind)
    | exact resolve eq3646 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3892 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3843 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq3843
    | (have j0 := eq3843 X0 X1
       grind)
    | exact resolve eq3843 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq3913 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3892 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3892
    | (have j0 := eq3892 X0 X1
       grind)
    | exact resolve eq3892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892
  have eq3927 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3913 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3913
    | (have j0 := eq3913 X0 X1
       grind)
    | exact resolve eq3913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913
  have eq3938 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3927 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3927
    | (have j0 := eq3927 X0 X1
       grind)
    | exact resolve eq3927 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3927
  have eq3943 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3938 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq3938
    | (have j0 := eq3938 X0 X1
       grind)
    | exact resolve eq3938 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq3938
  have eq14206 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3719
       grind)
    | exact superpose eq3719 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3719
       grind)
    | exact resolve eq12 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq14213 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq14206
  have eq65052 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14213
       grind)
    | exact superpose eq14213 eq16
    | exact resolve eq16 eq14213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14213
  have eq65099 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq65052
       have i₂ := eq3709
       grind)
    | exact superpose eq3709 eq65052
    | exact resolve eq65052 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709 eq65052
  have eq65100 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq65099
  have eq65101 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq65100
  have eq65584 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq81 x (σ y)
       have i₂ := eq65101
       grind)
    | exact superpose eq65101 eq81
    | (have j0 := eq81 x (σ y)
       grind)
    | (have r₁ := eq81 x (σ y)
       have r₂ := eq65101
       grind)
    | exact resolve eq81 eq65101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq65618 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq65584
  have eq65622 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq65618
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq65618
    | exact resolve eq65618 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65618
  have eq92949 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq65622
       grind)
    | exact superpose eq65622 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq65622
       grind)
    | exact resolve eq12 eq65622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65622
  have eq92967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq92949
  have eq92980 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq92967
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq92967
    | exact resolve eq92967 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92967
  have eq940076 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq65101
       have i₂ := eq92980
       grind)
    | exact superpose eq92980 eq65101
    | exact resolve eq65101 eq92980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65101 eq92980
  have eq940311 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq940076
  have eq940472 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3646 x y
       have i₂ := eq940311
       grind)
    | exact superpose eq940311 eq3646
    | (have j0 := eq3646 x y
       grind)
    | (have r₁ := eq3646 x y
       have r₂ := eq940311
       grind)
    | exact resolve eq3646 eq940311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940475 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3943 y x
       have i₂ := eq940311
       grind)
    | exact superpose eq940311 eq3943
    | (have j0 := eq3943 y x
       grind)
    | (have r₁ := eq3943 y x
       have r₂ := eq940311
       grind)
    | exact resolve eq3943 eq940311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940311
  have eq940727 : (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq940475
  have eq940729 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq940472
  have eq940738 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3646 x y
       grind)
    | (have r₁ := eq940729
       have r₂ := eq3646 x y
       grind)
    | exact resolve eq940729 eq3646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646 eq940729
  have eq944222 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq940738
       grind)
    | exact superpose eq940738 eq16
    | exact resolve eq16 eq940738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940738
  have eq947936 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq944222
       have i₂ := eq940727
       grind)
    | exact superpose eq940727 eq944222
    | exact resolve eq944222 eq940727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940727
  have eq947963 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq947936
  have eq948029 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq947963
       grind)
    | exact superpose eq947963 eq10
    | exact resolve eq10 eq947963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947963
  have eq948585 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq948029
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq948029
    | exact resolve eq948029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948029
  have eq952115 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3943 y x
       have i₂ := eq948585
       grind)
    | exact superpose eq948585 eq3943
    | (have j0 := eq3943 y x
       grind)
    | (have r₁ := eq3943 y x
       have r₂ := eq948585
       grind)
    | exact resolve eq3943 eq948585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943 eq948585
  have eq952367 : (M.op x y) = (M.op x x) := by grind
  clear eq952115
  have eq952407 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq944222
       have i₂ := eq952367
       grind)
    | exact superpose eq952367 eq944222
    | exact resolve eq944222 eq952367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944222 eq952367
  have eq952434 : False := by grind
  exact eq952434

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq75 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq70 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq70 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq124 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq5146 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq71 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq5147 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq5146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5146
  have eq5150 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5147 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5147
    | (have j0 := eq5147 X0
       grind)
    | exact resolve eq5147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5147
  have eq5155 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5150 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5150
    | exact resolve eq5150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150
  have eq5202 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5155 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq5155
    | (have j0 := eq5155 X0
       grind)
    | exact resolve eq5155 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5155
  have eq5205 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq5202 X0
       grind)
    | exact superpose eq5202 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq5202 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq5202 X0
       grind)
    | exact resolve eq12 eq5202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5202
  have eq5237 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq5260 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq5308 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5260 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq5260
    | (have j0 := eq5260 X0 X0
       grind)
    | exact resolve eq5260 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5260
  have eq5327 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq5237 X0 X1
       grind)
    | exact superpose eq5237 eq11
    | (have j1 := eq5237 X0 X1
       grind)
    | exact resolve eq11 eq5237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237
  have eq5438 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5327 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5327
    | (have j0 := eq5327 X0 X0
       grind)
    | exact resolve eq5327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327
  have eq5525 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5438 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5438
  have eq5526 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5525 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525
  have eq5745 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq5526 X0
       grind)
    | exact superpose eq5526 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq5526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq5756 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq121 X0 X0
       have i₂ := eq5526 X0
       grind)
    | exact superpose eq5526 eq121
    | (have j0 := eq121 X0 X0
       grind)
    | exact resolve eq121 eq5526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq5782 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5526 (σ X0)
       grind)
    | exact superpose eq5526 eq15
    | exact resolve eq15 eq5526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5816 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5848 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5782 X0
       have i₂ := eq5526 X0
       grind)
    | exact superpose eq5526 eq5782
    | exact resolve eq5782 eq5526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5526 eq5782
  have eq10545 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq5308 X0 X2
       grind)
    | exact superpose eq5308 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq5308 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq5308 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5308 X1 X1
       grind)
    | exact resolve eq12 eq5308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5308
  have eq10605 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10545 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10545
  have eq18508 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq10605 X0 X2 X1
       grind)
    | exact superpose eq10605 eq11
    | (have j1 := eq10605 X0 X2 X1
       grind)
    | exact resolve eq11 eq10605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10605
  have eq18650 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18508 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq18508
    | (have j0 := eq18508 X0 X1 X1
       grind)
    | exact resolve eq18508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18508
  have eq19123 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq18650 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18650
  have eq19124 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq19123 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19123
  have eq19331 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq19124 X1 (τ X0)
       grind)
    | exact superpose eq19124 eq18
    | (have j1 := eq19124 X1 (τ X0)
       grind)
    | exact resolve eq18 eq19124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq19382 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq19124 (σ X1) (σ X0)
       grind)
    | exact superpose eq19124 eq15
    | (have j1 := eq19124 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq19124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19124
  have eq22075 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19331 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19331
    | exact resolve eq19331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19331
  have eq22243 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22075 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq22075
    | (have j0 := eq22075 X0 X1
       grind)
    | exact resolve eq22075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22075
  have eq25073 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19382 x y
       grind)
    | exact superpose eq19382 eq16
    | (have j1 := eq19382 x y
       grind)
    | exact resolve eq16 eq19382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25175 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19382
  have eq25382 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25175 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq25175
    | (have j0 := eq25175 (τ X1) (τ X0)
       grind)
    | exact resolve eq25175 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq25475 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25382 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq25382
    | (have j0 := eq25382 X0 X1
       grind)
    | exact resolve eq25382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25382
  have eq25520 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25475 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25475
    | (have j0 := eq25475 X0 X1
       grind)
    | exact resolve eq25475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25475
  have eq25540 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25520 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25520
    | (have j0 := eq25520 X0 X1
       grind)
    | exact resolve eq25520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25520
  have eq25555 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25540 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25540
    | (have j0 := eq25540 X0 X1
       grind)
    | exact resolve eq25540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25540
  have eq26404 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25073
       have i₂ := eq22243 x y
       grind)
    | exact superpose eq22243 eq25073
    | (have j1 := eq22243 (σ x) (σ y)
       grind)
    | (have r₁ := eq25073
       have r₂ := eq22243 x y
       grind)
    | exact resolve eq25073 eq22243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22243 eq25073
  have eq26407 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26404
  have eq26412 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq26407
       grind)
    | exact superpose eq26407 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq26407
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26407
       grind)
    | exact resolve eq13 eq26407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26407
  have eq26429 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26412
  have eq33017 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25175 x y
       have i₂ := eq26429
       grind)
    | exact superpose eq26429 eq25175
    | (have j0 := eq25175 x y
       grind)
    | exact resolve eq25175 eq26429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25175 eq26429
  have eq33024 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33017
  have eq33025 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33024
  have eq33045 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33025
       grind)
    | exact superpose eq33025 eq16
    | exact resolve eq16 eq33025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33051 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq33025
       grind)
    | exact superpose eq33025 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq33025
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq33025
       grind)
    | exact resolve eq13 eq33025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33025
  have eq33068 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq33051
  have eq33071 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33068
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq33068
    | exact resolve eq33068 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33068
  have eq33074 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq33071
       have i₂ := eq5848 x
       grind)
    | exact superpose eq5848 eq33071
    | exact resolve eq33071 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33071
  have eq39587 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5816 x
       have i₂ := eq33074
       grind)
    | exact superpose eq33074 eq5816
    | (have j0 := eq5816 x
       grind)
    | (have r₁ := eq5816 x
       have r₂ := eq33074
       grind)
    | exact resolve eq5816 eq33074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33074
  have eq39645 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq39587
  have eq39690 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq5816 x
       grind)
    | (have r₁ := eq39645
       have r₂ := eq5816 x
       grind)
    | exact resolve eq39645 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39645
  have eq39711 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq39690
       have i₂ := eq5848 x
       grind)
    | exact superpose eq5848 eq39690
    | exact resolve eq39690 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39690
  have eq39728 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq39711
       grind)
    | exact superpose eq39711 eq10
    | exact resolve eq10 eq39711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39711
  have eq39897 : y = (k y x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq39728
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq39728
    | exact resolve eq39728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39728
  have eq40197 : y ≠ y ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq25555 y x
       have i₂ := eq39897
       grind)
    | exact superpose eq39897 eq25555
    | (have j0 := eq25555 y x
       grind)
    | (have r₁ := eq25555 y x
       have r₂ := eq39897
       grind)
    | exact resolve eq25555 eq39897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25555 eq39897
  have eq40206 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq40197
  have eq40220 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq33045
       have i₂ := eq40206
       grind)
    | exact superpose eq40206 eq33045
    | exact resolve eq33045 eq40206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33045 eq40206
  have eq40240 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq40220
  have eq40513 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq5745 x X0
       have i₂ := eq40240
       grind)
    | exact superpose eq40240 eq5745
    | (have j0 := eq5745 x X0
       grind)
    | (have r₁ := eq5745 x x
       have r₂ := eq40240
       grind)
    | exact resolve eq5745 eq40240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40520 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5816 x
       have i₂ := eq40240
       grind)
    | exact superpose eq40240 eq5816
    | (have j0 := eq5816 x
       grind)
    | (have r₁ := eq5816 x
       have r₂ := eq40240
       grind)
    | exact resolve eq5816 eq40240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40240
  have eq40578 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq40520
  have eq40585 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq40513 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40513
  have eq40623 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq5816 x
       grind)
    | (have r₁ := eq40578
       have r₂ := eq5816 x
       grind)
    | exact resolve eq40578 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5816 eq40578
  have eq40627 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq40585 X0
       have j1 := eq5745 x X0
       grind)
    | (have r₁ := eq40585 X0
       have r₂ := eq5745 x x
       grind)
    | exact resolve eq40585 eq5745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5745 eq40585
  have eq40644 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40623
       have i₂ := eq5848 x
       grind)
    | exact superpose eq5848 eq40623
    | exact resolve eq40623 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848 eq40623
  have eq40672 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq40644
       grind)
    | exact superpose eq40644 eq10
    | exact resolve eq10 eq40644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40644
  have eq40849 : x = (M.op x x) := by
    first
    | (have i₁ := eq40672
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40672
    | exact resolve eq40672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40672
  have eq41199 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq40849
       grind)
    | exact superpose eq40849 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq40849
       grind)
    | exact resolve eq12 eq40849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40849
  have eq41284 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq41199 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41199
  have eq42411 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq40627 (σ X0)
       grind)
    | exact superpose eq40627 eq15
    | exact resolve eq15 eq40627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40627
  have eq42513 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq42411 X0
       have i₂ := eq41284 X0
       grind)
    | exact superpose eq41284 eq42411
    | exact resolve eq42411 eq41284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41284 eq42411
  have eq43159 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42513 y
       grind)
    | exact superpose eq42513 eq16
    | (have r₁ := eq16
       have r₂ := eq42513 y
       grind)
    | exact resolve eq16 eq42513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42513
  have eq43287 : False := by grind
  exact eq43287

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq63 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq36
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq114
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq83
    | (have j0 := eq83 (σ y) (σ x)
       grind)
    | exact resolve eq83 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq142 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq64
    | exact resolve eq64 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq143 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq27
    | exact resolve eq27 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq69
    | (have r₁ := eq69
       have r₂ := eq128
       grind)
    | exact resolve eq69 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq128
  have eq321 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq320
  have eq322 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq321
       have r₂ := eq142
       grind)
    | exact resolve eq321 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq321
  have eq325 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq322 eq115
    | exact resolve eq115 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq322
  have eq329 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq325
  have eq334 : x = (M.op x y) := by
    first
    | (have r₁ := eq329
       have r₂ := eq143
       grind)
    | exact resolve eq329 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq329
  have eq337 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq334 eq20
    | exact resolve eq20 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq340 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq334 eq63
    | exact resolve eq63 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq341 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq334 eq68
    | (have r₁ := eq68
       have r₂ := eq334
       grind)
    | exact resolve eq68 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq334
  have eq346 : x = y ∨ x = (k y x) := by grind
  clear eq341
  have eq352 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq337
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq337
    | exact resolve eq337 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq357 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq352 eq26
    | exact resolve eq26 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq491 : x = (k y x) := by
    first
    | (have r₁ := eq346
       have r₂ := eq340
       grind)
    | exact resolve eq346 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq346
  have eq495 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq491
       grind)
    | exact superpose eq491 eq75
    | exact resolve eq75 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq491
  have eq502 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq352 eq495
    | exact resolve eq495 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq504 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq502
    | exact resolve eq502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq502
  have eq505 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq352 eq504
    | exact resolve eq504 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq504
  have eq508 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq505 eq83
    | (have j0 := eq83 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq83 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq505
  have eq509 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq508
  have eq511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq357 eq509
    | exact resolve eq509 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq509
  have eq514 : False := by grind
  exact eq514
