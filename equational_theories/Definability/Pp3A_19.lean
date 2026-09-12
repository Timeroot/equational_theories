import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq21 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq21 X0 x X2
       have i₂ := eq9 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X0)) = (k (M.op X0 X0) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq35 X0
       have i₂ := eq22 (M.op X0 X0) x
       grind)
    | exact superpose eq22 eq35
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq163 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) (M.op X1 X1)) ∨ (σ X0) = (k (σ X0) (M.op X1 X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X0
       have i₂ := eq58 X0 (σ X0)
       grind)
    | exact superpose eq58 eq85
    | (have j1 := eq58 X1 (σ X0)
       grind)
    | exact resolve eq85 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 y y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 (σ X0)
       have i₂ := eq85 X0 X0
       grind)
    | exact superpose eq85 eq58
    | (have j0 := eq58 X1 (σ X0)
       have j1 := eq85 X0 X0
       grind)
    | exact resolve eq58 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq177 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq179 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq186 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op X1 X1)) ∨ (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq264 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq177 (M.op X0 X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq177
    | (have j0 := eq177 (M.op X0 X0)
       grind)
    | exact resolve eq177 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq177 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq177
    | (have j0 := eq177 (τ X0)
       grind)
    | exact resolve eq177 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq269 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq264 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq271 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq268 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq268
    | (have j0 := eq268 X0
       grind)
    | exact resolve eq268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq271
    | (have j0 := eq271 X0
       grind)
    | exact resolve eq271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq281 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq274 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq274
    | (have j0 := eq274 (τ X0)
       grind)
    | exact resolve eq274 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq274
  have eq324 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ (M.op X0 X0)) x
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq22
    | exact resolve eq22 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ (M.op X0 X0)) X1
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq58
    | (have j0 := eq58 X1 (k X1 (σ (M.op X0 X0)))
       grind)
    | exact resolve eq58 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq281 (M.op X0 X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq281
    | (have j0 := eq281 (M.op X0 X0)
       grind)
    | exact resolve eq281 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq788 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq819 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ (M.op X0 X0)) x
       have i₂ := eq788 X0
       grind)
    | exact superpose eq788 eq22
    | exact resolve eq22 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (τ (M.op X0 X0)) X1
       have i₂ := eq788 X0
       grind)
    | exact superpose eq788 eq58
    | (have j0 := eq58 X1 (k X1 (τ (M.op X0 X0)))
       grind)
    | exact resolve eq58 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq164
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq164
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq164 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq852 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq851
  have eq1327 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq327 X1 (σ X0)
       grind)
    | exact superpose eq327 eq15
    | (have j1 := eq327 X1 (σ X0)
       grind)
    | exact resolve eq15 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq1745 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (σ (M.op X0 X0)) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X1) X0
       have i₂ := eq822 X1 X0
       grind)
    | exact superpose eq822 eq19
    | (have j1 := eq822 X1 X0
       grind)
    | exact resolve eq19 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq2838 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k (σ X1) (σ (M.op X0 X0))) ∨ (τ (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1745 X0 (σ (M.op X0 X0))
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq1745
    | exact resolve eq1745 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq2953 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (k X1 (M.op X0 X0))) ∨ (τ (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq15 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq2838
    | (have j0 := eq2838 X0 X1
       grind)
    | exact resolve eq2838 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq2967 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2953 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2953
    | (have j0 := eq2953 X0 X1
       grind)
    | exact resolve eq2953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq15722 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1327 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1327 X0 X1
       grind)
    | exact superpose eq1327 eq10
    | (have j1 := eq1327 X0 X1
       grind)
    | exact resolve eq10 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq15779 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15722 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15722
    | (have j0 := eq15722 X0 X1
       grind)
    | exact resolve eq15722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15722
  have eq16095 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2967 X1 X0
       have i₂ := eq15779 X0 X1
       grind)
    | exact superpose eq15779 eq2967
    | (have j0 := eq2967 (σ X0) (σ (M.op X0 X0))
       have j1 := eq15779 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq2967 eq15779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq16100 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq15779 (τ X0) X1
       grind)
    | exact superpose eq15779 eq18
    | (have j1 := eq15779 (k X0 (σ (M.op X1 X1))) (σ (τ X0))
       grind)
    | exact resolve eq18 eq15779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15779
  have eq16138 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq16095 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16095
  have eq16156 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16100 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16100
    | (have j0 := eq16100 X0 X1
       grind)
    | exact resolve eq16100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16100
  have eq16551 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16138 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16138
    | (have j0 := eq16138 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq16138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16138
  have eq17265 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16156 X0 (τ (M.op X0 X0))
       have i₂ := eq788 X0
       grind)
    | exact superpose eq788 eq16156
    | exact resolve eq16156 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17386 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X2 (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X1 X1
       have i₂ := eq16156 X0 X1
       grind)
    | exact superpose eq16156 eq324
    | (have j1 := eq16156 X0 X1
       grind)
    | exact resolve eq324 eq16156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16156
  have eq17530 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17386 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17386
    | (have j0 := eq17386 X0 X1 X2
       grind)
    | exact resolve eq17386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17386
  have eq17549 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17265 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq17265
    | (have j0 := eq17265 X0 X1
       grind)
    | exact resolve eq17265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17265
  have eq17609 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0
       have i₂ := eq17530 X0 X1 X0
       grind)
    | exact superpose eq17530 eq36
    | (have j1 := eq17530 X0 X1 x
       grind)
    | exact resolve eq36 eq17530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530
  have eq18011 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (σ X0)
       have i₂ := eq17609 (σ X0) X1
       grind)
    | exact superpose eq17609 eq44
    | (have j1 := eq17609 (σ X0) X1
       grind)
    | exact resolve eq44 eq17609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17609
  have eq18075 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18011 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18011
    | (have j0 := eq18011 X0 X1
       grind)
    | exact resolve eq18011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18011
  have eq18122 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18075 X0 X1
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq18075
    | (have j0 := eq18075 X0 X1
       grind)
    | exact resolve eq18075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18075
  have eq18370 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X2 (τ X0)) ∨ (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq819 X0 X1
       have i₂ := eq17549 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq819 X0 X1
       have i₂ := eq17549 X0 X1
       grind)
    | exact superpose eq17549 eq819
    | (have j1 := eq17549 X1 X0
       grind)
    | exact resolve eq819 eq17549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549
  have eq18743 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 (τ X0) X1
       have i₂ := eq18370 X0 X1 (τ X0)
       grind)
    | exact superpose eq18370 eq324
    | (have j1 := eq18370 X0 X2 X2
       grind)
    | exact resolve eq324 eq18370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18370
  have eq18825 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18743 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18743
    | (have j0 := eq18743 X0 X1 X2
       grind)
    | exact resolve eq18743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18743
  have eq18965 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18825 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825
  have eq19450 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq16551 X0 X1
       grind)
    | exact superpose eq16551 eq10
    | (have j1 := eq16551 (M.op X0 X0) (τ X0)
       grind)
    | exact resolve eq10 eq16551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16551
  have eq22087 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq19450 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19450
  have eq23999 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq36
    | (have j1 := eq179 X0 X1
       grind)
    | exact resolve eq36 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq24100 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23999 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq23999
    | (have j0 := eq23999 X0 X1
       grind)
    | exact resolve eq23999 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23999
  have eq28274 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq28298 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq28274 X0 X1
       have j1 := eq24100 X0 X1
       grind)
    | (have r₁ := eq28274 X0 X1
       have r₂ := eq24100 X0 X1
       grind)
    | exact resolve eq28274 eq24100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24100 eq28274
  have eq28618 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = (k (σ (τ X0)) (M.op X1 X1)) ∨ (σ (τ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq28298 (τ X0) X1
       grind)
    | exact superpose eq28298 eq18
    | (have j1 := eq28298 (τ X0) X1
       grind)
    | exact resolve eq18 eq28298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28633 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k X0 X0) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq28298 X0 X1
       grind)
    | exact superpose eq28298 eq10
    | (have j1 := eq28298 X0 X1
       grind)
    | exact resolve eq10 eq28298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28298
  have eq28723 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (k X0 (τ (M.op X1 X1))) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28633 X0 X1
       have i₂ := eq44 X0 (M.op X1 X1)
       grind)
    | exact superpose eq44 eq28633
    | (have j0 := eq28633 X0 X1
       grind)
    | exact resolve eq28633 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq28633
  have eq28734 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) ∨ (σ (τ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28618 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28618
    | (have j0 := eq28618 X0 X1
       grind)
    | exact resolve eq28618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28618
  have eq28817 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28734 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28734
    | (have j0 := eq28734 X0 X1
       grind)
    | exact resolve eq28734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28734
  have eq28960 : ∀ X0 X1 : G, (k X1 X1) = (k X1 (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28817 X0 (τ (M.op X0 X0))
       have i₂ := eq788 X0
       grind)
    | exact superpose eq788 eq28817
    | exact resolve eq28817 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq29174 : ∀ X0 X1 : G, (σ (k (τ X0) (M.op X1 X1))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq28817 (τ X0) X1
       grind)
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq28817 (τ X0) X1
       grind)
    | exact superpose eq28817 eq18
    | (have j1 := eq28817 (τ X0) X1
       grind)
    | exact resolve eq18 eq28817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28817
  have eq29272 : ∀ X0 X1 : G, (σ (k (τ X0) (M.op X1 X1))) = (k X0 X0) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29174 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29174
    | (have j0 := eq29174 X0 X1
       grind)
    | exact resolve eq29174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29174
  have eq29350 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ (M.op X1 X1))) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29272 X0 X1
       have i₂ := eq18 X0 (M.op X1 X1)
       grind)
    | exact superpose eq18 eq29272
    | (have j0 := eq29272 X0 X1
       grind)
    | exact resolve eq29272 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29272
  have eq33999 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X1) = (k X1 (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28723 X0 (σ (M.op X0 X0))
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq28723
    | exact resolve eq28723 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28723
  have eq34439 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33999 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq33999
    | (have j0 := eq33999 X0 X1
       grind)
    | exact resolve eq33999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33999
  have eq34521 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq269 y
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq269
    | exact resolve eq269 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq852
  have eq34568 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq34521
  have eq38706 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = (σ (k (τ X0) (τ (M.op X1 X1)))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq28960 X1 (τ X0)
       grind)
    | (have i₁ := eq18 X0 (τ (M.op X0 X0))
       have i₂ := eq28960 X0 (τ X0)
       grind)
    | exact superpose eq28960 eq18
    | (have j1 := eq28960 X1 (τ X0)
       grind)
    | exact resolve eq18 eq28960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28960
  have eq38878 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = (k (σ (τ X0)) (M.op X1 X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38706 X0 X1
       have i₂ := eq19 (M.op X1 X1) (τ X0)
       grind)
    | exact superpose eq19 eq38706
    | (have j0 := eq38706 X0 X1
       grind)
    | exact resolve eq38706 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38706
  have eq39023 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38878 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38878
    | (have j0 := eq38878 X0 X1
       grind)
    | exact resolve eq38878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38878
  have eq44626 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq34439 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq324 X0 X1
       have i₂ := eq34439 X0 X1
       grind)
    | exact superpose eq34439 eq324
    | (have j1 := eq34439 X1 X0
       grind)
    | exact resolve eq324 eq34439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34439
  have eq51385 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X1 (τ (σ X0))) ∨ (k X0 (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq819 (σ X0) X1
       have i₂ := eq44626 X0 X1 (σ X0)
       grind)
    | exact superpose eq44626 eq819
    | (have j1 := eq44626 X0 X2 X2
       grind)
    | exact resolve eq819 eq44626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51419 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22087 (σ X0)
       have i₂ := eq44626 X0 X1 (σ X0)
       grind)
    | exact superpose eq44626 eq22087
    | (have j0 := eq22087 (σ X0)
       have j1 := eq44626 X0 X1 x
       grind)
    | exact resolve eq22087 eq44626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22087 eq44626
  have eq51484 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51419 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51419
  have eq51510 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51484 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51484
    | (have j0 := eq51484 X0 X1
       grind)
    | exact resolve eq51484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51484
  have eq51525 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (k X0 (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51385 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51385
    | (have j0 := eq51385 X0 X1 X2
       grind)
    | exact resolve eq51385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51385
  have eq51791 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0
       have i₂ := eq51525 X0 X0 x
       grind)
    | exact superpose eq51525 eq36
    | (have j1 := eq51525 X0 X1 X1
       grind)
    | exact resolve eq36 eq51525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq51525
  have eq52926 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq51510 X0 X1
       grind)
    | exact superpose eq51510 eq37
    | (have j1 := eq51510 X0 X1
       grind)
    | exact resolve eq37 eq51510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq51510
  have eq68419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52926 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52926
  have eq68430 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68419 X0
       have j1 := eq51791 X0 X0
       grind)
    | (have r₁ := eq68419 X0
       have r₂ := eq51791 X0 x
       grind)
    | exact resolve eq68419 eq51791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51791 eq68419
  have eq68610 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq68430 (τ X0)
       grind)
    | exact superpose eq68430 eq18
    | exact resolve eq18 eq68430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq68430
  have eq68670 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq68610 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq68610
    | exact resolve eq68610 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68610
  have eq68718 : ∀ X0 : G, (k X0 X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq68670 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68670
    | exact resolve eq68670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68670
  have eq69011 : ∀ X0 X1 : G, (k X1 X1) = (k X1 (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) ∨ (k X1 (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68718 X0
       have i₂ := eq39023 X0 X1
       grind)
    | (have i₁ := eq68718 (M.op X1 X1)
       have i₂ := eq39023 X0 X1
       grind)
    | exact superpose eq39023 eq68718
    | (have j1 := eq39023 X1 X0
       grind)
    | exact resolve eq68718 eq39023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39023
  have eq69012 : ∀ X0 X1 : G, (k X1 X1) = (k X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (k X1 (σ (M.op X0 X0))) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68718 X0
       have i₂ := eq29350 X0 X1
       grind)
    | exact superpose eq29350 eq68718
    | (have j1 := eq29350 X1 (M.op X0 X0)
       grind)
    | exact resolve eq68718 eq29350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29350 eq68718
  have eq69298 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (k X1 X1) ∨ (k X1 (σ (M.op X0 X0))) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69012 X0 X1
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq69012 X0 X1
       have i₂ := eq22 (M.op X0 X0) x
       grind)
    | exact superpose eq22 eq69012
    | (have j0 := eq69012 X0 X1
       grind)
    | exact resolve eq69012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69012
  have eq69299 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69298
  have eq69300 : ∀ X0 X1 : G, (k X1 X1) = (k X1 (σ (τ (M.op X0 X0)))) ∨ (k X1 (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69011 X0 X1
       have i₂ := eq819 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq819 eq69011
    | (have j0 := eq69011 X0 X1
       grind)
    | exact resolve eq69011 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq69011
  have eq69357 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (k X1 X1) ∨ (k X1 (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69300 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq69300
    | (have j0 := eq69300 X0 X1
       grind)
    | exact resolve eq69300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69300
  have eq69358 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69357
  have eq70297 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69358 X1 (σ X0)
       grind)
    | exact superpose eq69358 eq15
    | exact resolve eq15 eq69358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71010 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (σ X0) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69299 X1 (σ X0)
       grind)
    | (have i₁ := eq15 X0 (M.op X0 X0)
       have i₂ := eq69299 X0 (σ X0)
       grind)
    | exact superpose eq69299 eq15
    | exact resolve eq15 eq69299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69299
  have eq71128 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71010 X0 X1
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq71010
    | exact resolve eq71010 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71010
  have eq76531 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op X2 X2)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70297 X0 X2
       have i₂ := eq69358 X1 X0
       grind)
    | (have i₁ := eq70297 (M.op X0 X0) X1
       have i₂ := eq69358 X0 (M.op X0 X0)
       grind)
    | exact superpose eq69358 eq70297
    | exact resolve eq70297 eq69358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70297
  have eq77930 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 (M.op X1 X1))) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71128 X0 X1
       have i₂ := eq18122 X0 X2
       grind)
    | exact superpose eq18122 eq71128
    | (have j1 := eq18122 X0 X2
       grind)
    | exact resolve eq71128 eq18122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18122
  have eq105068 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 (M.op X1 X1))) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18965 (σ X0) x
       have i₂ := eq76531 X0 X1 x
       grind)
    | exact superpose eq76531 eq18965
    | exact resolve eq18965 eq76531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18965 eq76531
  have eq105294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq105068 X0 X1
       have j1 := eq77930 X0 X1 X1
       grind)
    | (have r₁ := eq105068 X0 X1
       have r₂ := eq77930 X0 X1 x
       grind)
    | exact resolve eq105068 eq77930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77930 eq105068
  have eq106053 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71128 X0 x
       have i₂ := eq105294 X0 x
       grind)
    | exact superpose eq105294 eq71128
    | exact resolve eq71128 eq105294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71128
  have eq107063 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq106053 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106053
    | exact resolve eq106053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107611 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq107063 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq107063
    | exact resolve eq107063 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq107063
  have eq107667 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq107611 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107611
    | exact resolve eq107611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107611
  have eq107866 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69358 X1 X0
       have i₂ := eq107667 X0
       grind)
    | exact superpose eq107667 eq69358
    | exact resolve eq69358 eq107667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69358
  have eq111816 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105294 X0 x
       have i₂ := eq107866 X0 x
       grind)
    | exact superpose eq107866 eq105294
    | exact resolve eq105294 eq107866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105294 eq107866
  have eq120517 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq111816
  have eq120789 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq120517 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq120517
    | exact resolve eq120517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120517
  have eq120909 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq120789
  have eq1181634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq120909 y
       have i₂ := eq34568
       grind)
    | exact superpose eq34568 eq120909
    | exact resolve eq120909 eq34568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34568
  have eq1181962 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1181634
       have r₂ := eq16
       grind)
    | exact resolve eq1181634 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181634
  have eq1182429 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1181962
       have i₂ := eq106053 y
       grind)
    | exact superpose eq106053 eq1181962
    | exact resolve eq1181962 eq106053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181962
  have eq1182893 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1182429
       have i₂ := eq107667 y
       grind)
    | exact superpose eq107667 eq1182429
    | exact resolve eq1182429 eq107667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182429
  have eq1183358 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1182893
       have i₂ := eq106053 y
       grind)
    | exact superpose eq106053 eq1182893
    | exact resolve eq1182893 eq106053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106053 eq1182893
  have eq1183742 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1183358
       have i₂ := eq107667 y
       grind)
    | exact superpose eq107667 eq1183358
    | exact resolve eq1183358 eq107667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107667 eq1183358
  have eq1245166 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1183742
       grind)
    | exact superpose eq1183742 eq10
    | exact resolve eq10 eq1183742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183742
  have eq1245593 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1245166
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1245166
    | exact resolve eq1245166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245166
  have eq1247583 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1245593
       grind)
    | exact superpose eq1245593 eq10
    | exact resolve eq10 eq1245593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245593
  have eq1248010 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1247583
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1247583
    | exact resolve eq1247583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247583
  have eq1253556 : ∀ X0 : G, x = (M.op y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22 y x
       have i₂ := eq1248010
       grind)
    | exact superpose eq1248010 eq22
    | exact resolve eq22 eq1248010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1248010
  have eq1261032 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq120909 y
       have i₂ := eq1253556 X0
       grind)
    | exact superpose eq1253556 eq120909
    | (have j1 := eq1253556 X0
       grind)
    | exact resolve eq120909 eq1253556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120909 eq1253556
  have eq1261291 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1261032 X0
       grind)
    | (have r₁ := eq1261032 X0
       have r₂ := eq16
       grind)
    | exact resolve eq1261032 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261032
  have eq1261509 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq324 y x
       have i₂ := eq1261291 y
       grind)
    | exact superpose eq1261291 eq324
    | exact resolve eq324 eq1261291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq1264264 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1261509 (σ x)
       grind)
    | exact superpose eq1261509 eq16
    | exact resolve eq16 eq1261509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261509
  have eq1264327 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1264264
       have i₂ := eq1261291 x
       grind)
    | exact superpose eq1261291 eq1264264
    | exact resolve eq1264264 eq1261291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261291 eq1264264
  have eq1264328 : False := by grind
  exact eq1264328

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq39
    | exact resolve eq39 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq39
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 (M.op X1 X1) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X2 (M.op (M.op X0 X1) X2)) (M.op X2 X0)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq182 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq73 (M.op X0 X1) (k X0 X1) x
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq73 X0 X1 X0
       grind)
    | (have r₁ := eq180 X1 X0
       have r₂ := eq73 X0 X1 X1
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq73 (M.op X0 X1) (M.op X0 X0) x
       grind)
    | exact resolve eq180 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq180
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq182 (σ X0) (σ X1)
       grind)
    | exact superpose eq182 eq15
    | (have j1 := eq182 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq182 (τ X0) X1
       grind)
    | exact superpose eq182 eq18
    | (have j1 := eq182 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq182
  have eq613 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq613
    | (have j0 := eq613 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq613 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq1378 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 x y
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 x y
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1378
       have i₂ := eq642 x y
       grind)
    | exact superpose eq642 eq1378
    | (have j1 := eq642 (σ x) (σ y)
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 x y
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1378 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1378
  have eq1417 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1416
  have eq1465 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1417
       grind)
    | exact superpose eq1417 eq16
    | exact resolve eq16 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1466 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1465
       have r₂ := eq44 x
       grind)
    | exact resolve eq1465 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1467 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq16
    | exact resolve eq16 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1468 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq10
    | exact resolve eq10 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1507 : x = y := by
    first
    | (have i₁ := eq1468
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1468
    | exact resolve eq1468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1508 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq44 x
       grind)
    | exact superpose eq44 eq1467
    | exact resolve eq1467 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1467
  have eq1509 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq1508
    | exact resolve eq1508 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq1508
  have eq1510 : False := by grind
  exact eq1510

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq76 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X2 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq21 X0 X0 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq76 X0 X1 X2 X3
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq76 X0 X1 X1 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq76 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq106 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 X1 X2 x
       have i₂ := eq21 x X0 X1 X0
       grind)
    | exact superpose eq21 eq99
    | (have j0 := eq99 X0 X1 X2 x
       grind)
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq99
  have eq129 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq132 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X1
       have j1 := eq106 X0 X1 X1
       grind)
    | (have r₁ := eq129 x X0
       have r₂ := eq106 X0 X0 x
       grind)
    | (have r₁ := eq129 X0 x
       have r₂ := eq106 X0 x x
       grind)
    | exact resolve eq129 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq129
  have eq285 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq132 (σ X1) (σ X0)
       grind)
    | exact superpose eq132 eq15
    | exact resolve eq15 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq132 X1 X0
       grind)
    | exact superpose eq132 eq285
    | exact resolve eq285 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq285
  have eq294 : False := by grind
  exact eq294

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq70
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | (have i₁ := eq81 X0
       have i₂ := eq14 (σ X0) (σ X0)
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 (σ (M.op X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq371 X0 X1
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq371 (M.op X0 X0) (M.op (σ X0) X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq371 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq371
  have eq386 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq376
    | exact resolve eq376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq376 X0 (σ X1)
       grind)
    | exact superpose eq376 eq15
    | (have j1 := eq376 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq426 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq386 (τ X0) X1
       grind)
    | exact superpose eq386 eq19
    | (have j1 := eq386 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq386
  have eq513 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq426 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq426
    | exact resolve eq426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq552 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq513
    | (have j0 := eq513 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq692 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq397 x y
       grind)
    | exact superpose eq397 eq16
    | (have j1 := eq397 x y
       grind)
    | exact resolve eq16 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq692
       have i₂ := eq552 x y
       grind)
    | exact superpose eq552 eq692
    | (have j1 := eq552 (σ x) (σ y)
       grind)
    | (have r₁ := eq692
       have r₂ := eq552 x y
       grind)
    | (have r₁ := eq692
       have r₂ := eq552 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq692
       have r₂ := eq552 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq692 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq692
  have eq710 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq709
  have eq726 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq710
       grind)
    | exact superpose eq710 eq16
    | exact resolve eq16 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq727 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq726
       have r₂ := eq81 x
       grind)
    | exact resolve eq726 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq728 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq16
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq10
    | exact resolve eq10 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq769 : x = y := by
    first
    | (have i₁ := eq729
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq729
    | exact resolve eq729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq770 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq728
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq728
    | exact resolve eq728 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq728
  have eq771 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq770
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq770
    | exact resolve eq770 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq770
  have eq772 : False := by grind
  exact eq772

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pyy_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq284
    | exact resolve eq284 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq284
  have eq347 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq348 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq348 X0 X1
       grind)
    | exact resolve eq347 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq368 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq349 X0 (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 X0 (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq398 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq303 X1
       grind)
    | exact superpose eq303 eq379
    | (have j0 := eq379 X0 X1
       grind)
    | exact resolve eq379 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq379
  have eq416 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq368 (τ X0) X1
       grind)
    | exact superpose eq368 eq19
    | (have j1 := eq368 (τ X0) X1
       grind)
    | exact resolve eq19 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq368
  have eq553 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq416 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq416
    | exact resolve eq416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq859 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq398 x y
       grind)
    | exact superpose eq398 eq16
    | (have j1 := eq398 x y
       grind)
    | exact resolve eq16 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq898 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq594 x y
       grind)
    | exact superpose eq594 eq859
    | (have j1 := eq594 x y
       grind)
    | (have r₁ := eq859
       have r₂ := eq594 x y
       grind)
    | exact resolve eq859 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq899 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq898
  have eq907 : x = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq899
       grind)
    | exact superpose eq899 eq9
    | exact resolve eq9 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq912 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq907
       grind)
    | exact superpose eq907 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq907
       grind)
    | exact resolve eq12 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq914 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq859
       have i₂ := eq914 y
       grind)
    | exact superpose eq914 eq859
    | exact resolve eq859 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq914
  have eq926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq925
  have eq927 : (σ x) = (σ (M.op y y)) := by grind
  clear eq926
  have eq930 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq10
    | exact resolve eq10 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq974 : x = (M.op y y) := by
    first
    | (have i₁ := eq930
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq930
    | exact resolve eq930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq988 : x = (M.op x x) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq9
    | exact resolve eq9 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq991 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq348 x X0
       have i₂ := eq988
       grind)
    | exact superpose eq988 eq348
    | (have j0 := eq348 x X0
       grind)
    | exact resolve eq348 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq992 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq988
       grind)
    | exact superpose eq988 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq988
       grind)
    | exact resolve eq12 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq994 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq995 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq991 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1074 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq995 (σ X0)
       grind)
    | exact superpose eq995 eq15
    | exact resolve eq15 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1094 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1074 X0
       have i₂ := eq994 X0
       grind)
    | exact superpose eq994 eq1074
    | exact resolve eq1074 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994 eq1074
  have eq1238 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1094 y
       grind)
    | exact superpose eq1094 eq16
    | (have r₁ := eq16
       have r₂ := eq1094 y
       grind)
    | exact resolve eq16 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1248 : False := by grind
  exact eq1248

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq19
  have eq40 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
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
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X1 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | (have j0 := eq53 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq53 (τ X1) (τ X0)
       grind)
    | exact superpose eq53 eq44
    | (have j1 := eq53 (τ X0) (τ X1)
       grind)
    | exact resolve eq44 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq53
  have eq552 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq916 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq42 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq921 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq916 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq916
    | exact resolve eq916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq943 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq921 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq921
    | exact resolve eq921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq973 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq943 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq943
    | exact resolve eq943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1045 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq973 X0
       grind)
    | exact superpose eq973 eq723
    | exact resolve eq723 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq973
  have eq208017 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq11
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq208114 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208017 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208017
    | (have j0 := eq208017 X0 X1
       grind)
    | exact resolve eq208017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208017
  have eq208191 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208114 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq208114
    | (have j0 := eq208114 (τ (k (σ X0) X1)) (M.op (τ X1) X0)
       grind)
    | exact resolve eq208114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208114
  have eq208588 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208191 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq208191
    | (have j0 := eq208191 X0 X1
       grind)
    | exact resolve eq208191 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq208191
  have eq208624 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq208588 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq208588
    | (have j0 := eq208588 X0 (σ X1)
       grind)
    | exact resolve eq208588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208588
  have eq208771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq552
       have i₂ := eq208624 x y
       grind)
    | exact superpose eq208624 eq552
    | (have j1 := eq208624 x y
       grind)
    | (have r₁ := eq552
       have r₂ := eq208624 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq552
       have r₂ := eq208624 (k y x) (M.op x y)
       grind)
    | exact resolve eq552 eq208624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq208624
  have eq208772 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq208771
  have eq208773 : (σ x) = (σ y) := by grind
  clear eq208772
  have eq210473 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq208773
       grind)
    | exact superpose eq208773 eq10
    | exact resolve eq10 eq208773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208773
  have eq210576 : x = y := by
    first
    | (have i₁ := eq210473
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq210473
    | exact resolve eq210473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210473
  have eq210609 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq210576
       grind)
    | exact superpose eq210576 eq16
    | exact resolve eq16 eq210576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210576
  have eq210610 : False := by grind
  exact eq210610

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_y_pyx_Equation3735 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3735 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X1)
       have i₂ := eq9 X1 X1 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq9 X1 X1 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq66 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq64 X0 (σ X1)
       grind)
    | exact superpose eq64 eq28
    | exact resolve eq28 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 X0) (M.op X0 X2)
       grind)
    | (have r₁ := eq13 (M.op X1 X0) (M.op X0 X1)
       have r₂ := eq9 X0 X1 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq105
    | exact resolve eq105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X2 X0 (M.op X0 X1)
       have i₂ := eq61 X0 X2 X1 X2
       grind)
    | exact superpose eq61 eq117
    | exact resolve eq117 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 X0 X1 (M.op X1 X2)
       have i₂ := eq117 X1 X0 X2
       grind)
    | exact superpose eq117 eq152
    | exact resolve eq152 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X2)
       have i₂ := eq152 X0 X2 X1
       grind)
    | exact superpose eq152 eq13
    | (have j0 := eq13 X1 (M.op X0 X2)
       grind)
    | (have r₁ := eq13 X2 (M.op X0 X2)
       have r₂ := eq152 X0 X2 X2
       grind)
    | exact resolve eq13 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq152 X0 X2 (M.op X0 X2)
       grind)
    | exact superpose eq152 eq181
    | (have j0 := eq181 X0 X1 X2
       grind)
    | exact resolve eq181 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq297 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq118 X0 X1
       grind)
    | exact superpose eq118 eq9
    | (have j1 := eq118 X0 X1
       grind)
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = (k X1 (τ (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) X1
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq66
    | (have j1 := eq118 X0 X0
       grind)
    | exact resolve eq66 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq313 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq118 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq315 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq319 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = (k X1 (τ (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq323 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq319
    | (have j0 := eq319 X0 X1
       grind)
    | exact resolve eq319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq331 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq297 X0 X1 X2
       have i₂ := eq175 (σ (k X0 X1)) X2 (σ X1)
       grind)
    | exact superpose eq175 eq297
    | (have j0 := eq297 X0 X1 X2
       grind)
    | exact resolve eq297 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq539 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1 X2
       have i₂ := eq152 X0 X2 (M.op X0 X2)
       grind)
    | exact superpose eq152 eq100
    | (have j0 := eq100 X0 X1 X2
       grind)
    | exact resolve eq100 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq540 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X0 X0) ∨ (M.op X0 X2) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X0 X1 X2
       have i₂ := eq175 X0 X0 X2
       grind)
    | exact superpose eq175 eq539
    | (have j0 := eq539 X0 X1 X2
       grind)
    | (have r₁ := eq539 X0 X1 (M.op X1 X2)
       have r₂ := eq175 X0 X1 X2
       grind)
    | (have r₁ := eq539 X0 (M.op X1 X2) X1
       have r₂ := eq175 X0 X1 X2
       grind)
    | exact resolve eq539 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq670 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq540 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1142 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k X1 (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq323 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq323
    | (have j0 := eq323 (τ X0) X1
       grind)
    | exact resolve eq323 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq1174 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k X1 (τ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1142 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1142
    | (have j0 := eq1142 X0 X1
       grind)
    | exact resolve eq1142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1207 : ∀ X0 : G, (σ (τ (k X0 X0))) ≠ (σ (τ (k X0 X0))) ∨ (σ (τ (k X0 X0))) = (M.op (σ (τ (k X0 X0))) (σ (τ (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq315 (τ (k X0 X0))
       have i₂ := eq1174 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq1174 eq315
    | (have j0 := eq315 (τ (k X0 X0))
       have j1 := eq1174 (σ (τ (k X0 X0))) x
       grind)
    | exact resolve eq315 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq1174
  have eq1219 : ∀ X0 : G, (σ (τ (k X0 X0))) = (M.op (σ (τ (k X0 X0))) (σ (τ (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1225 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1219 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1219
    | (have j0 := eq1219 (k X0 X0)
       grind)
    | exact resolve eq1219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq2485 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X1 X0))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq313 (M.op X0 X1) (M.op X1 X0)
       have i₂ := eq670 X0 X1
       grind)
    | exact superpose eq670 eq313
    | (have j0 := eq313 (M.op X0 X1) (M.op X1 X0)
       have j1 := eq670 X0 X1
       grind)
    | exact resolve eq313 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq670
  have eq2500 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X1 X0))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2485 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq4089 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq331 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq331
    | (have j0 := eq331 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq331 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq4158 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4089 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4089
    | (have j0 := eq4089 X0 X1 X2
       grind)
    | exact resolve eq4089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4165 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4158 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4158
    | (have j0 := eq4158 X0 X1 X2
       grind)
    | exact resolve eq4158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq4170 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4165 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4165
    | (have j0 := eq4165 X0 X1 X2
       grind)
    | exact resolve eq4165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165
  have eq4171 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4170 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4170
    | (have j0 := eq4170 (σ (τ X1)) X1 X2
       grind)
    | exact resolve eq4170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq4172 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4171 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4171
    | (have j0 := eq4171 X0 X1 X2
       grind)
    | exact resolve eq4171 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4171
  have eq4187 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1225 X0
       have i₂ := eq4172 X0 X0 (k X0 X0)
       grind)
    | exact superpose eq4172 eq1225
    | (have j0 := eq1225 X0
       have j1 := eq4172 X0 X0 x
       grind)
    | exact resolve eq1225 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq4172
  have eq4228 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4187
  have eq4293 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 X0 (k X0 X0)
       have i₂ := eq4228 X0
       grind)
    | exact superpose eq4228 eq175
    | (have j1 := eq4228 X0
       grind)
    | exact resolve eq175 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4443 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4228 X0
       have i₂ := eq4293 X0 X0
       grind)
    | exact superpose eq4293 eq4228
    | (have j0 := eq4228 X0
       have j1 := eq4293 X0 x
       grind)
    | exact resolve eq4228 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228 eq4293
  have eq4489 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4443 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4496 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4489 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4489 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4489 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq4600 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4496 (σ X0)
       grind)
    | exact superpose eq4496 eq15
    | exact resolve eq15 eq4496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4606 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq4496 (τ X0)
       grind)
    | exact superpose eq4496 eq31
    | exact resolve eq31 eq4496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4617 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4606 X0
       have i₂ := eq4496 X0
       grind)
    | exact superpose eq4496 eq4606
    | exact resolve eq4606 eq4496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606
  have eq4623 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4600 X0
       have i₂ := eq4496 X0
       grind)
    | exact superpose eq4496 eq4600
    | exact resolve eq4600 eq4496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4496 eq4600
  have eq4724 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (τ X0) (τ X0) X1
       have i₂ := eq4617 X0
       grind)
    | exact superpose eq4617 eq152
    | exact resolve eq152 eq4617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4814 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (σ X0) (σ X0) X1
       have i₂ := eq4623 X0
       grind)
    | exact superpose eq4623 eq152
    | exact resolve eq152 eq4623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4816 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (σ X0) (σ X0)
       have i₂ := eq4623 X0
       grind)
    | exact superpose eq4623 eq175
    | exact resolve eq175 eq4623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4881 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (M.op (τ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4724 (M.op X0 X1) X2
       have i₂ := eq152 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq152 eq4724
    | exact resolve eq4724 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4973 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4881 X0 X1 X2
       have i₂ := eq175 X0 X0 X1
       grind)
    | exact superpose eq175 eq4881
    | exact resolve eq4881 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4881
  have eq4995 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4973 X0 X1 X2
       have i₂ := eq4724 X0 X2
       grind)
    | exact superpose eq4724 eq4973
    | exact resolve eq4973 eq4724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724 eq4973
  have eq5185 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4814 (M.op X0 X1) X2
       have i₂ := eq152 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq152 eq4814
    | exact resolve eq4814 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5294 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5185 X0 X1 X2
       have i₂ := eq175 X0 X0 X1
       grind)
    | exact superpose eq175 eq5185
    | exact resolve eq5185 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5185
  have eq5321 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5294 X0 X1 X2
       have i₂ := eq4814 X0 X2
       grind)
    | exact superpose eq4814 eq5294
    | exact resolve eq5294 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814 eq5294
  have eq5350 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4816 (M.op X0 X1) X2
       have i₂ := eq152 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq152 eq4816
    | exact resolve eq4816 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5476 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X0))) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5350 X0 X1 X2
       have i₂ := eq175 X0 X0 X1
       grind)
    | exact superpose eq175 eq5350
    | exact resolve eq5350 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq5501 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5476 X0 X1 X2
       have i₂ := eq4816 X0 X2
       grind)
    | exact superpose eq4816 eq5476
    | exact resolve eq5476 eq4816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4816 eq5476
  have eq80017 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2500 X0 X1
       have i₂ := eq5501 X1 X0 (σ (M.op X0 X1))
       grind)
    | exact superpose eq5501 eq2500
    | (have j0 := eq2500 X0 X1
       grind)
    | exact resolve eq2500 eq5501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq80018 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80017 X0 X1
       have i₂ := eq5321 X0 X1 (σ X1)
       grind)
    | exact superpose eq5321 eq80017
    | (have j0 := eq80017 X0 X1
       grind)
    | exact resolve eq80017 eq5321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80017
  have eq80019 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80018 X0 X1
       have i₂ := eq5501 X0 X1 (σ (M.op X0 X1))
       grind)
    | exact superpose eq5501 eq80018
    | (have j0 := eq80018 X0 X1
       grind)
    | exact resolve eq80018 eq5501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501 eq80018
  have eq80020 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80019 X0 X1
       have i₂ := eq5321 X0 X1 (σ X0)
       grind)
    | exact superpose eq5321 eq80019
    | (have j0 := eq80019 X0 X1
       grind)
    | exact resolve eq80019 eq5321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5321 eq80019
  have eq80021 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80020 X0 X1
       have i₂ := eq4623 X0
       grind)
    | exact superpose eq4623 eq80020
    | (have j0 := eq80020 X0 X1
       grind)
    | exact resolve eq80020 eq4623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80020
  have eq84348 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80021 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80021
    | (have j0 := eq80021 X1 (τ X0)
       grind)
    | exact resolve eq80021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80021
  have eq1620072 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X0 X0) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197 X0 X1 X2
       have i₂ := eq175 X0 X0 X2
       grind)
    | exact superpose eq175 eq197
    | (have j0 := eq197 X0 X1 X2
       grind)
    | (have r₁ := eq197 X0 X1 (M.op X1 X2)
       have r₂ := eq175 X0 X1 X2
       grind)
    | (have r₁ := eq197 X0 (M.op X1 X2) X1
       have r₂ := eq175 X0 X1 X2
       grind)
    | exact resolve eq197 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1620444 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1620072 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620072
  have eq1621435 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 (σ X1))
       have i₂ := eq1620444 X0 (σ X1)
       grind)
    | exact superpose eq1620444 eq28
    | (have j1 := eq1620444 X0 (σ X1)
       grind)
    | exact resolve eq28 eq1620444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2099108 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (M.op X1 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq4617 X1
       grind)
    | exact superpose eq4617 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq4617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq2100000 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2099108 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099108
  have eq2521462 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq84348 X1 X0
       grind)
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq84348 X0 X1
       grind)
    | exact superpose eq84348 eq10
    | (have j1 := eq84348 X1 X0
       grind)
    | exact resolve eq10 eq84348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84348
  have eq2522338 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2521462 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2521462
    | (have j0 := eq2521462 X0 X1
       grind)
    | exact resolve eq2521462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521462
  have eq2522339 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2522338 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522338
  have eq2526301 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq2522339 X0 X1
       grind)
    | exact superpose eq2522339 eq10
    | (have j1 := eq2522339 X0 X1
       grind)
    | exact resolve eq10 eq2522339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522339
  have eq2530924 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2526301 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2526301
    | (have j0 := eq2526301 (τ X0) X1
       grind)
    | exact resolve eq2526301 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526301
  have eq2532285 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2530924 X0 X1
       have i₂ := eq4617 X0
       grind)
    | exact superpose eq4617 eq2530924
    | (have j0 := eq2530924 X0 X1
       grind)
    | exact resolve eq2530924 eq4617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4617 eq2530924
  have eq2585504 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq2532285 X0 X1
       grind)
    | exact superpose eq2532285 eq11
    | (have j1 := eq2532285 X0 X1
       grind)
    | exact resolve eq11 eq2532285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2586523 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2532285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532285
  have eq2596757 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2585504 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2585504
    | exact resolve eq2585504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585504
  have eq2599988 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq2596757 X1 X0
       grind)
    | exact superpose eq2596757 eq11
    | (have j1 := eq2596757 X1 X0
       grind)
    | exact resolve eq11 eq2596757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596757
  have eq2601944 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2599988 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2599988
    | exact resolve eq2599988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599988
  have eq2603451 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2601944 X0 X1
       have i₂ := eq4623 X0
       grind)
    | exact superpose eq4623 eq2601944
    | (have j0 := eq2601944 X0 X1
       grind)
    | exact resolve eq2601944 eq4623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601944
  have eq2616413 : ∀ X0 X1 : G, (τ (σ (M.op X0 X1))) = (k X1 (τ (σ (M.op X0 X1)))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1621435 (σ X0) X1
       have i₂ := eq2603451 X0 X1
       grind)
    | exact superpose eq2603451 eq1621435
    | (have j1 := eq2603451 X0 X1
       grind)
    | exact resolve eq1621435 eq2603451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621435 eq2603451
  have eq2617032 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2616413 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2616413
    | (have j0 := eq2616413 X0 X1
       grind)
    | exact resolve eq2616413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616413
  have eq2617722 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2617032 X0 X1
       have i₂ := eq4623 X0
       grind)
    | exact superpose eq4623 eq2617032
    | (have j0 := eq2617032 X0 X1
       grind)
    | exact resolve eq2617032 eq4623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4623 eq2617032
  have eq2617723 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2617722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617722
  have eq2619778 : ∀ X0 X1 X2 : G, (τ (k X1 (σ (M.op X0 X0)))) = (k (τ X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 (M.op X0 X2)
       have i₂ := eq2617723 X0 X2
       grind)
    | (have i₁ := eq22 X0 (M.op X0 X0)
       have i₂ := eq2617723 X0 X1
       grind)
    | exact superpose eq2617723 eq22
    | (have j1 := eq2617723 X0 X2
       grind)
    | exact resolve eq22 eq2617723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617723
  have eq2620678 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X0 X0)) = (k (τ X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2619778 X0 X1 X2
       have i₂ := eq22 X1 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq2619778
    | (have j0 := eq2619778 X0 X1 X2
       grind)
    | exact resolve eq2619778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2619778
  have eq2621653 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (τ X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2620678 X0 X1 X2
       have i₂ := eq64 X0 (τ X1)
       grind)
    | exact superpose eq64 eq2620678
    | (have j0 := eq2620678 X0 X1 X2
       grind)
    | exact resolve eq2620678 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq2620678
  have eq2673389 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2621653 X1 X1 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621653
  have eq2673444 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2673389 X0 X1
       have j1 := eq1620444 X1 (τ X0)
       grind)
    | (have r₁ := eq2673389 X0 (τ X0)
       have r₂ := eq1620444 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq2673389 X0 X0
       have r₂ := eq1620444 X0 (τ X0)
       grind)
    | exact resolve eq2673389 eq1620444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620444 eq2673389
  have eq2676166 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2673444 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2673444
    | exact resolve eq2673444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673444
  have eq2678415 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op (M.op X0 X1) (M.op X0 X1))) = (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2100000 (M.op X0 X1) X1
       have i₂ := eq2676166 X1 X0
       grind)
    | exact superpose eq2676166 eq2100000
    | (have j0 := eq2100000 (M.op X0 X1) X1
       grind)
    | exact resolve eq2100000 eq2676166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100000 eq2676166
  have eq2678839 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) (M.op X0 X1))) = (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2678415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678415
  have eq2679066 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2678839 X0 X1
       have i₂ := eq152 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq152 eq2678839
    | (have j0 := eq2678839 X0 X1
       grind)
    | exact resolve eq2678839 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2678839
  have eq2679452 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2679066 X0 X1
       have i₂ := eq175 X0 X0 X1
       grind)
    | exact superpose eq175 eq2679066
    | (have j0 := eq2679066 X0 X1
       grind)
    | exact resolve eq2679066 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2679066
  have eq2679660 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2679452 X0 X1
       have i₂ := eq4995 X0 X1 (τ X1)
       grind)
    | exact superpose eq4995 eq2679452
    | (have j0 := eq2679452 X0 X1
       grind)
    | exact resolve eq2679452 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995 eq2679452
  have eq2679781 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2679660 X0 X1
       have j1 := eq2586523 X0 X1
       grind)
    | (have r₁ := eq2679660 X0 X1
       have r₂ := eq2586523 X0 X1
       grind)
    | (have r₁ := eq2679660 X1 X1
       have r₂ := eq2586523 X1 X1
       grind)
    | exact resolve eq2679660 eq2586523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586523 eq2679660
  have eq2680050 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2679781 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2679781
    | exact resolve eq2679781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679781
  have eq2683457 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq2680050 X0 X1
       grind)
    | exact superpose eq2680050 eq11
    | exact resolve eq11 eq2680050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680050
  have eq2688143 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2683457 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2683457
    | exact resolve eq2683457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683457
  have eq2694682 : False := by grind
  exact eq2694682

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq332 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq12
    | (have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq348 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq360 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq552 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq360 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq360
    | exact resolve eq360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq360 x y
       grind)
    | exact superpose eq360 eq16
    | (have j1 := eq360 x y
       grind)
    | exact resolve eq16 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq360 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq592 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq552
  have eq735 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq592
    | exact resolve eq592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq800 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq735 (τ X1) X0
       grind)
    | exact superpose eq735 eq17
    | (have j1 := eq735 (τ X1) X0
       grind)
    | exact resolve eq17 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq735
  have eq1104 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq800
    | exact resolve eq800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq1147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1104
    | (have j0 := eq1104 X0 X1
       grind)
    | exact resolve eq1104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq563
       have i₂ := eq1147 y x
       grind)
    | exact superpose eq1147 eq563
    | (have j1 := eq1147 (σ y) (σ x)
       grind)
    | (have r₁ := eq563
       have r₂ := eq1147 y x
       grind)
    | exact resolve eq563 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1288 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1287
  have eq1334 : x ≠ x ∨ x = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1288
       grind)
    | exact superpose eq1288 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1288
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1288
       grind)
    | exact resolve eq13 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : x = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1334
  have eq3146 : x ≠ (M.op x y) ∨ x = (k y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1339
       grind)
    | exact superpose eq1339 eq12
    | exact resolve eq12 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq3159 : x ≠ (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3146
  have eq3162 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3159
       have r₂ := eq1288
       grind)
    | exact resolve eq3159 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq3159
  have eq3167 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq578 x y
       have i₂ := eq3162
       grind)
    | exact superpose eq3162 eq578
    | (have j0 := eq578 x y
       grind)
    | exact resolve eq578 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq3162
  have eq3188 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3167
  have eq3189 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3188
  have eq3285 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3189
       grind)
    | exact superpose eq3189 eq16
    | exact resolve eq16 eq3189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3292 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3189
       grind)
    | exact superpose eq3189 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3189
       grind)
    | exact resolve eq13 eq3189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3304 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq3292
  have eq3316 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3304
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3304
    | exact resolve eq3304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq3475 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3316
       grind)
    | exact superpose eq3316 eq12
    | exact resolve eq12 eq3316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq3508 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq3475
       have r₂ := eq3189
       grind)
    | exact resolve eq3475 eq3189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189 eq3475
  have eq3533 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3508
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3508
    | exact resolve eq3508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508
  have eq3534 : (σ x) = (σ (k y x)) := by grind
  clear eq3533
  have eq3699 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1147 y x
       have i₂ := eq3534
       grind)
    | exact superpose eq3534 eq1147
    | (have j0 := eq1147 y x
       grind)
    | exact resolve eq1147 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq3534
  have eq3771 : x = (M.op x y) := by
    first
    | (have r₁ := eq3699
       have r₂ := eq3285
       grind)
    | exact resolve eq3699 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3939 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3285
       have i₂ := eq3771
       grind)
    | exact superpose eq3771 eq3285
    | exact resolve eq3285 eq3771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285 eq3771
  have eq3957 : False := by grind
  exact eq3957
