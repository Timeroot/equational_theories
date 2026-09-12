import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq32
    | exact resolve eq32 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq80 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq73
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq104 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq63
    | exact resolve eq63 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq624 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq607 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq607
    | (have j0 := eq607 X0 X1
       grind)
    | exact resolve eq607 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq624
  have eq3020 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq638 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq638
    | exact resolve eq638 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq3123 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3020 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3020
    | (have j0 := eq3020 X0 X1
       grind)
    | exact resolve eq3020 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020
  have eq3145 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3123 X0 X1
       have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq3123 (M.op X1 (σ X0)) X0
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq3123 X1 X0
       have r₂ := eq103 X0 X1
       grind)
    | exact resolve eq3123 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq3123
  have eq3149 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3145 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3145
    | (have j0 := eq3145 X1 (τ X0)
       grind)
    | exact resolve eq3145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3145 (σ X0) X1
       grind)
    | exact superpose eq3145 eq15
    | (have j1 := eq3145 (σ X0) X1
       grind)
    | exact resolve eq15 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3228 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3149 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq3149
    | (have j0 := eq3149 X0 X1
       grind)
    | exact resolve eq3149 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq3149
  have eq3229 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3228 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3228
    | (have j0 := eq3228 X0 X1
       grind)
    | exact resolve eq3228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3274 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq3229 X1 (τ X0)
       grind)
    | exact superpose eq3229 eq18
    | (have j1 := eq3229 X1 (τ X0)
       grind)
    | exact resolve eq18 eq3229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3229
  have eq3788 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3274 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3274
    | exact resolve eq3274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3870 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3788 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3788
    | (have j0 := eq3788 X0 X1
       grind)
    | exact resolve eq3788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq4230 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3178 x y
       grind)
    | exact superpose eq3178 eq16
    | (have j1 := eq3178 x y
       grind)
    | exact resolve eq16 eq3178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq4357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4230
       have i₂ := eq3870 x y
       grind)
    | exact superpose eq3870 eq4230
    | (have j1 := eq3870 x y
       grind)
    | (have r₁ := eq4230
       have r₂ := eq3870 x y
       grind)
    | exact resolve eq4230 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870
  have eq4358 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4357
  have eq4365 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq4358
       grind)
    | exact superpose eq4358 eq63
    | exact resolve eq63 eq4358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4366 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq68 y
       have i₂ := eq4358
       grind)
    | exact superpose eq4358 eq68
    | exact resolve eq68 eq4358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq4358
  have eq4394 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4230
       have i₂ := eq4366
       grind)
    | exact superpose eq4366 eq4230
    | exact resolve eq4230 eq4366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4230 eq4366
  have eq4399 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4394
  have eq4400 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4399
       have i₂ := eq4365
       grind)
    | exact superpose eq4365 eq4399
    | exact resolve eq4399 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365 eq4399
  have eq4401 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4400
  have eq4402 : (σ x) = (σ (M.op y y)) := by grind
  clear eq4401
  have eq4404 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq4402
       grind)
    | exact superpose eq4402 eq104
    | exact resolve eq104 eq4402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq4411 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4402
       grind)
    | exact superpose eq4402 eq10
    | exact resolve eq10 eq4402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402
  have eq4462 : x = (M.op y y) := by
    first
    | (have i₁ := eq4411
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4411
    | exact resolve eq4411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4411
  have eq4467 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq4462
       grind)
    | exact superpose eq4462 eq63
    | exact resolve eq63 eq4462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4462
  have eq4506 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4404
       grind)
    | exact superpose eq4404 eq16
    | exact resolve eq16 eq4404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4404
  have eq4519 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4506
       have i₂ := eq4467
       grind)
    | exact superpose eq4467 eq4506
    | exact resolve eq4506 eq4467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467 eq4506
  have eq4520 : False := by grind
  exact eq4520

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq32
    | exact resolve eq32 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq80 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq73
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq104 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq63
    | exact resolve eq63 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq613 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq596
    | (have j0 := eq596 X0 X1
       grind)
    | exact resolve eq596 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq627 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq613
    | (have j0 := eq613 X0 X1
       grind)
    | exact resolve eq613 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq613
  have eq3020 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq627 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq627
    | exact resolve eq627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq3123 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3020 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3020
    | (have j0 := eq3020 X0 X1
       grind)
    | exact resolve eq3020 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020
  have eq3145 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3123 X0 X1
       have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq3123 (M.op X1 (σ X0)) X0
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq3123 X1 X0
       have r₂ := eq103 X0 X1
       grind)
    | exact resolve eq3123 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq3123
  have eq3149 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3145 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3145
    | (have j0 := eq3145 X1 (τ X0)
       grind)
    | exact resolve eq3145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3145 (σ X0) X1
       grind)
    | exact superpose eq3145 eq15
    | (have j1 := eq3145 (σ X0) X1
       grind)
    | exact resolve eq15 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3228 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3149 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq3149
    | (have j0 := eq3149 X0 X1
       grind)
    | exact resolve eq3149 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq3149
  have eq3229 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3228 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3228
    | (have j0 := eq3228 X0 X1
       grind)
    | exact resolve eq3228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3274 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq3229 X1 (τ X0)
       grind)
    | exact superpose eq3229 eq18
    | (have j1 := eq3229 X1 (τ X0)
       grind)
    | exact resolve eq18 eq3229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3229
  have eq3788 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3274 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3274
    | exact resolve eq3274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3870 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3788 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3788
    | (have j0 := eq3788 X0 X1
       grind)
    | exact resolve eq3788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq4230 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3178 x y
       grind)
    | exact superpose eq3178 eq16
    | (have j1 := eq3178 x y
       grind)
    | exact resolve eq16 eq3178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq4358 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4230
       have i₂ := eq3870 x y
       grind)
    | exact superpose eq3870 eq4230
    | (have j1 := eq3870 x y
       grind)
    | (have r₁ := eq4230
       have r₂ := eq3870 x y
       grind)
    | exact resolve eq4230 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870
  have eq4359 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4358
  have eq4366 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq4359
       grind)
    | exact superpose eq4359 eq63
    | exact resolve eq63 eq4359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4367 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq68 y
       have i₂ := eq4359
       grind)
    | exact superpose eq4359 eq68
    | exact resolve eq68 eq4359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq4359
  have eq4395 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4230
       have i₂ := eq4367
       grind)
    | exact superpose eq4367 eq4230
    | exact resolve eq4230 eq4367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4230 eq4367
  have eq4400 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4395
  have eq4401 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4400
       have i₂ := eq4366
       grind)
    | exact superpose eq4366 eq4400
    | exact resolve eq4400 eq4366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4366 eq4400
  have eq4402 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4401
  have eq4403 : (σ x) = (σ (M.op y y)) := by grind
  clear eq4402
  have eq4405 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq4403
       grind)
    | exact superpose eq4403 eq104
    | exact resolve eq104 eq4403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq4412 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4403
       grind)
    | exact superpose eq4403 eq10
    | exact resolve eq10 eq4403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4403
  have eq4463 : x = (M.op y y) := by
    first
    | (have i₁ := eq4412
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4412
    | exact resolve eq4412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412
  have eq4468 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq4463
       grind)
    | exact superpose eq4463 eq63
    | exact resolve eq63 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4463
  have eq4507 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4405
       grind)
    | exact superpose eq4405 eq16
    | exact resolve eq16 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405
  have eq4520 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4507
       have i₂ := eq4468
       grind)
    | exact superpose eq4468 eq4507
    | exact resolve eq4507 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468 eq4507
  have eq4521 : False := by grind
  exact eq4521

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq586 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq605 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq586 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq586
    | (have j0 := eq586 X0 X1
       grind)
    | exact resolve eq586 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq616 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq605
    | exact resolve eq605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq637 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq616
    | (have j0 := eq616 X0 X1
       grind)
    | exact resolve eq616 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq616
  have eq639 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq637 X1 X0
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq637 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq103 X0 X1
       grind)
    | exact resolve eq637 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq637
  have eq641 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq639 (σ X0) X1
       grind)
    | exact superpose eq639 eq15
    | (have j1 := eq639 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq684 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq641 (τ X1) X0
       grind)
    | exact superpose eq641 eq19
    | (have j1 := eq641 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq641
  have eq768 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq684
    | exact resolve eq684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq816 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq768
    | (have j0 := eq768 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq999 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654 x y
       grind)
    | exact superpose eq654 eq16
    | (have j1 := eq654 x y
       grind)
    | exact resolve eq16 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq999
       have i₂ := eq816 y x
       grind)
    | exact superpose eq816 eq999
    | (have j1 := eq816 (σ x) (σ y)
       grind)
    | (have r₁ := eq999
       have r₂ := eq816 y x
       grind)
    | (have r₁ := eq999
       have r₂ := eq816 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq999
       have r₂ := eq816 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq999 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq999
  have eq1018 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1017
  have eq1021 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1018
       grind)
    | exact superpose eq1018 eq16
    | exact resolve eq16 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1022 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1021
       have r₂ := eq82 x
       grind)
    | exact resolve eq1021 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1023 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq16
    | exact resolve eq16 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq10
    | exact resolve eq10 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1070 : x = y := by
    first
    | (have i₁ := eq1024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1024
    | exact resolve eq1024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1071 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1023
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq1023
    | exact resolve eq1023 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1023
  have eq1072 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq1071
    | exact resolve eq1071 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1071
  have eq1073 : False := by grind
  exact eq1073

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq103 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq586 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq605 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq586 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq586
    | (have j0 := eq586 X0 X1
       grind)
    | exact resolve eq586 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq616 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq605
    | exact resolve eq605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq637 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq616
    | (have j0 := eq616 X0 X1
       grind)
    | exact resolve eq616 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq616
  have eq639 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq637 X1 X0
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq637 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq103 X0 X1
       grind)
    | exact resolve eq637 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq637
  have eq641 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq639 (σ X0) X1
       grind)
    | exact superpose eq639 eq15
    | (have j1 := eq639 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq684 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq641 (τ X1) X0
       grind)
    | exact superpose eq641 eq19
    | (have j1 := eq641 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq641
  have eq768 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq684
    | exact resolve eq684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq816 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq768
    | (have j0 := eq768 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq999 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654 x y
       grind)
    | exact superpose eq654 eq16
    | (have j1 := eq654 x y
       grind)
    | exact resolve eq16 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq999
       have i₂ := eq816 y x
       grind)
    | exact superpose eq816 eq999
    | (have j1 := eq816 (σ x) (σ y)
       grind)
    | (have r₁ := eq999
       have r₂ := eq816 y x
       grind)
    | (have r₁ := eq999
       have r₂ := eq816 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq999
       have r₂ := eq816 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq999 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq999
  have eq1018 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1017
  have eq1021 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1018
       grind)
    | exact superpose eq1018 eq16
    | exact resolve eq16 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1022 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1021
       have r₂ := eq82 x
       grind)
    | exact resolve eq1021 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1023 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq16
    | exact resolve eq16 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq10
    | exact resolve eq10 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1070 : x = y := by
    first
    | (have i₁ := eq1024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1024
    | exact resolve eq1024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1071 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1023
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq1023
    | exact resolve eq1023 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1023
  have eq1072 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq1071
    | exact resolve eq1071 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1071
  have eq1073 : False := by grind
  exact eq1073

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq12
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq20 X0
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq30 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq83 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq159 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq66
    | exact resolve eq66 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq66 x x
       grind)
    | exact superpose eq66 eq20
    | (have j1 := eq66 X0 X0
       grind)
    | exact resolve eq20 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq171 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq174 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq205 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X1 X2
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq320 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq333 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq320 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq320
    | (have j0 := eq320 X0
       grind)
    | exact resolve eq320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq337 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq333
    | (have j0 := eq333 X0
       grind)
    | exact resolve eq333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq357 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq12
    | (have j1 := eq337 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq337 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq337 X0
       grind)
    | exact resolve eq12 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq358 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq357 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq649 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq686 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq649 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq649
    | (have j0 := eq649 X0 X1
       grind)
    | exact resolve eq649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq935 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq171 (τ X0) (τ X1)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq171
    | (have j0 := eq171 (τ X0) (τ X1)
       grind)
    | exact resolve eq171 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq935 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq935
    | (have j0 := eq935 X0 X1
       grind)
    | exact resolve eq935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq950 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq945 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq945
    | (have j0 := eq945 X0 X1
       grind)
    | exact resolve eq945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq954 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq950
    | (have j0 := eq950 X0 X1
       grind)
    | exact resolve eq950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq956 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq954
    | (have j0 := eq954 X0 X1
       grind)
    | exact resolve eq954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq957 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq958 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq957
    | (have j0 := eq957 X0 X1
       grind)
    | exact resolve eq957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1067 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (τ X0) (τ X1)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq172
    | (have j0 := eq172 (τ X0) (τ X1)
       grind)
    | exact resolve eq172 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1067 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1067
    | (have j0 := eq1067 X0 X1
       grind)
    | exact resolve eq1067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1093 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1088 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1088
    | (have j0 := eq1088 X0 X1
       grind)
    | exact resolve eq1088 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1097 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1093 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1093
    | (have j0 := eq1093 X0 X1
       grind)
    | exact resolve eq1093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1099 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1097 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1097
    | (have j0 := eq1097 X0 X1
       grind)
    | exact resolve eq1097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1100 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1099 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1099
    | (have j0 := eq1099 X0 X1
       grind)
    | exact resolve eq1099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1101 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1100
    | (have j0 := eq1100 X0 X1
       grind)
    | exact resolve eq1100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1208 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq100 x X2 X0 X1
       grind)
    | exact superpose eq100 eq30
    | exact resolve eq30 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1209 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq100 x X2 X0 X1
       grind)
    | exact superpose eq100 eq9
    | exact resolve eq9 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1285 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1209 x X1 X0
       grind)
    | exact superpose eq1209 eq9
    | exact resolve eq9 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1209 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1209 eq9
    | exact resolve eq9 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1209 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1209 eq1208
    | exact resolve eq1208 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1366 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (M.op X0 (σ X1)) X1
       have i₂ := eq1291 (σ X1) X0
       grind)
    | exact superpose eq1291 eq26
    | exact resolve eq26 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1367 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (τ X1))
       have i₂ := eq1291 (τ X1) X0
       grind)
    | exact superpose eq1291 eq18
    | exact resolve eq18 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2507 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq159 X0 X1 X2
       grind)
    | exact superpose eq159 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq159 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq159 X0 X1 X2
       grind)
    | exact resolve eq13 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2515 : ∀ X0 X1 X2 : G, (σ X0) ≠ (k X1 (σ X2)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq159 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq2516 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2507 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2517 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2516 X0 X1 X2
       have j1 := eq2515 X2 X0 X1
       grind)
    | (have r₁ := eq2516 X1 X2 X0
       have r₂ := eq2515 X0 X1 X2
       grind)
    | exact resolve eq2516 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq2516
  have eq2543 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2517 X0 X1 X2
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq2517
    | (have j0 := eq2517 X0 X1 X2
       grind)
    | exact resolve eq2517 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2517
  have eq5475 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1209 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1290 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1290 eq1209
    | exact resolve eq1209 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq1290
  have eq5552 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq5475 X0 X1 X2
       grind)
    | exact superpose eq5475 eq83
    | exact resolve eq83 eq5475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq5475
  have eq6075 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op X3 (τ X0))))
       have i₂ := eq5552 (τ X0) X2 X3 X1
       grind)
    | exact superpose eq5552 eq17
    | exact resolve eq17 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552
  have eq6084 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6075 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6075
    | exact resolve eq6075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6075
  have eq6474 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ X0)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ X0))))))
       have i₂ := eq6084 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq6084 eq17
    | exact resolve eq17 eq6084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6084
  have eq6490 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ X0)))))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6474 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6474
    | exact resolve eq6474 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6474
  have eq7738 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ (τ X0)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ (τ X0))))))))
       have i₂ := eq6490 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq6490 eq17
    | exact resolve eq17 eq6490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6490
  have eq7768 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ (τ X0)))))))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7738 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7738
    | exact resolve eq7738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7738
  have eq10863 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ (τ (τ X0)))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ (τ (τ X0))))))))))
       have i₂ := eq7768 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq7768 eq17
    | exact resolve eq17 eq7768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10901 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X3 (τ (τ (τ (τ X0)))))))))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10863 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10863
    | exact resolve eq10863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10863
  have eq19548 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 (σ X0)
       have i₂ := eq205 (σ X0) X0 X0
       grind)
    | exact superpose eq205 eq29
    | (have j1 := eq205 (σ X0) X0 x
       grind)
    | exact resolve eq29 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq205
  have eq19577 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq19548 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19548
  have eq19585 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19577 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19577
    | (have j0 := eq19577 X0
       grind)
    | exact resolve eq19577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577
  have eq19651 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq19585 (τ X0)
       grind)
    | exact superpose eq19585 eq18
    | (have j1 := eq19585 (τ X0)
       grind)
    | exact resolve eq18 eq19585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19585
  have eq19728 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19651 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq19651
    | (have j0 := eq19651 X0
       grind)
    | exact resolve eq19651 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19651
  have eq19743 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19728 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19728
    | (have j0 := eq19728 X0
       grind)
    | exact resolve eq19728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19728
  have eq19754 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19743 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19743
    | (have j0 := eq19743 X0
       grind)
    | exact resolve eq19743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19743
  have eq19792 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq358 X0
       have i₂ := eq19754 X0
       grind)
    | exact superpose eq19754 eq358
    | (have j0 := eq358 X0
       have j1 := eq19754 X0
       grind)
    | exact resolve eq358 eq19754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq19754
  have eq19858 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19792
  have eq19904 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq19858 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq19858 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq19858 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19858
  have eq20206 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq172 X0 X0
       have i₂ := eq19904 X0
       grind)
    | exact superpose eq19904 eq172
    | (have j0 := eq172 X0 X0
       grind)
    | exact resolve eq172 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20237 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq19904 (σ X0)
       grind)
    | exact superpose eq19904 eq15
    | exact resolve eq15 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20247 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq19904 (τ X0)
       grind)
    | exact superpose eq19904 eq40
    | exact resolve eq40 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20277 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20206
  have eq20303 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20247 X0
       have i₂ := eq19904 X0
       grind)
    | exact superpose eq19904 eq20247
    | exact resolve eq20247 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20247
  have eq20311 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20237 X0
       have i₂ := eq19904 X0
       grind)
    | exact superpose eq19904 eq20237
    | exact resolve eq20237 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237
  have eq20521 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (τ (M.op (τ (τ X0)) (τ (τ X0)))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7768 X0 X1 X2 (τ (τ (τ X0)))
       have i₂ := eq20303 (τ (τ X0))
       grind)
    | exact superpose eq20303 eq7768
    | exact resolve eq7768 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768
  have eq20522 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10901 X0 X1 X2 (τ (τ (τ (τ X0))))
       have i₂ := eq20303 (τ (τ (τ X0)))
       grind)
    | exact superpose eq20303 eq10901
    | exact resolve eq10901 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10901
  have eq20599 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (M.op (τ (τ X0)) (τ (τ X0)))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20522 X0 X1 X2
       have i₂ := eq20303 (τ (τ X0))
       grind)
    | exact superpose eq20303 eq20522
    | exact resolve eq20522 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20522
  have eq20600 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (M.op (τ X0) (τ X0)))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20521 X0 X1 X2
       have i₂ := eq20303 (τ X0)
       grind)
    | exact superpose eq20303 eq20521
    | exact resolve eq20521 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20521
  have eq20626 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (τ (M.op (τ X0) (τ X0)))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20599 X0 X1 X2
       have i₂ := eq20303 (τ X0)
       grind)
    | exact superpose eq20303 eq20599
    | exact resolve eq20599 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20599
  have eq20627 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (τ (M.op X0 X0)))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20600 X0 X1 X2
       have i₂ := eq20303 X0
       grind)
    | exact superpose eq20303 eq20600
    | exact resolve eq20600 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20600
  have eq20642 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (τ (τ (M.op X0 X0)))))))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20626 X0 X1 X2
       have i₂ := eq20303 X0
       grind)
    | exact superpose eq20303 eq20626
    | exact resolve eq20626 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20626
  have eq34245 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (τ (τ (M.op X0 X0))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20627 (τ X0) X1 X2
       have i₂ := eq20303 X0
       grind)
    | exact superpose eq20303 eq20627
    | exact resolve eq20627 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20627
  have eq117941 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op X2 (M.op X3 (τ (τ (τ (τ (M.op X0 X0))))))))))))) ∨ (M.op X0 X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op X2 (M.op X3 (τ (τ (τ (τ (M.op X0 X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2543 X0 (σ (σ (σ (M.op X1 (M.op X2 (τ (τ (τ (τ (M.op X0 X0)))))))))) X2
       have i₂ := eq20642 X0 X1 X2
       grind)
    | exact superpose eq20642 eq2543
    | exact resolve eq2543 eq20642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq20642
  have eq118135 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op X2 (M.op X3 (τ (τ (τ (τ (M.op X0 X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq117941 X0 X1 X2 X3
       have i₂ := eq34245 X0 X2 X3
       grind)
    | exact superpose eq34245 eq117941
    | (have j0 := eq117941 X0 X1 X2 X3
       grind)
    | exact resolve eq117941 eq34245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117941
  have eq118277 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op X2 (M.op X3 (τ (τ (τ (τ (M.op X0 X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118135 X0 X1 X2 X3
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq118135
    | (have j0 := eq118135 X0 X1 X2 X3
       grind)
    | exact resolve eq118135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118135
  have eq118418 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k X1 (k (τ X0) (σ (σ (σ (M.op X2 (M.op X3 (τ (τ (τ (τ (M.op X0 X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq118277 X0 X1 X2 X3
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq118277 X1 X1 X2 X3
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq118277 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118277
  have eq118551 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118418 X0 X1 x x
       have i₂ := eq34245 X0 x x
       grind)
    | exact superpose eq34245 eq118418
    | (have j0 := eq118418 X0 X1 x x
       grind)
    | exact resolve eq118418 eq34245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34245 eq118418
  have eq118648 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118551 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq118551
    | (have j0 := eq118551 X0 X1
       grind)
    | exact resolve eq118551 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118551
  have eq118958 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq118648 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq118648
    | exact resolve eq118648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118998 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq118648 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq118648
    | exact resolve eq118648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119076 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq118648 X1 X0
       grind)
    | exact superpose eq118648 eq37
    | (have j1 := eq118648 X1 X0
       grind)
    | exact resolve eq37 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq119319 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq118648 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119498 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq118998 X0 X1
       have i₂ := eq20311 X1
       grind)
    | exact superpose eq20311 eq118998
    | (have j0 := eq118998 X0 X1
       grind)
    | exact resolve eq118998 eq20311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118998
  have eq120447 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq118958 (τ X0) X1
       grind)
    | exact superpose eq118958 eq17
    | (have j1 := eq118958 (τ X0) X1
       grind)
    | exact resolve eq17 eq118958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123832 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq119076 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq119076
    | exact resolve eq119076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123978 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (k (k X0 (τ (σ X1))) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1366 (σ X0) X1
       have i₂ := eq119076 X0 (σ X1)
       grind)
    | exact superpose eq119076 eq1366
    | (have j1 := eq119076 X0 (σ X1)
       grind)
    | exact resolve eq1366 eq119076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119076
  have eq124169 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123978 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123978
    | (have j0 := eq123978 X0 X1
       grind)
    | exact resolve eq123978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123978
  have eq124232 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123832 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq123832
    | (have j0 := eq123832 X0 X1
       grind)
    | exact resolve eq123832 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123832
  have eq124250 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (k (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124169 X0 X1
       have i₂ := eq20311 X1
       grind)
    | exact superpose eq20311 eq124169
    | (have j0 := eq124169 X0 X1
       grind)
    | exact resolve eq124169 eq20311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124169
  have eq124298 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124250 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq124250
    | (have j0 := eq124250 X0 X1
       grind)
    | exact resolve eq124250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124250
  have eq124601 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X2 (k X0 X1)
       have i₂ := eq124232 X0 X1
       grind)
    | exact superpose eq124232 eq40
    | (have j1 := eq124232 X0 X1
       grind)
    | exact resolve eq40 eq124232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124232
  have eq124821 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124601 X0 X1 X2
       have i₂ := eq40 X2 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq124601
    | (have j0 := eq124601 X0 X1 X2
       grind)
    | exact resolve eq124601 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124601
  have eq125990 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120447 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120447
    | exact resolve eq120447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120447
  have eq126386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq125990 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq125990
    | (have j0 := eq125990 X0 X1
       grind)
    | exact resolve eq125990 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125990
  have eq128614 : ∀ X0 X1 : G, (τ (k X0 X1)) = (k (τ (k X0 X1)) (τ X1)) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq124298 (τ X1) (τ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq124298
    | exact resolve eq124298 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124298
  have eq128885 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (k X0 X1) X1)) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq128614 X0 X1
       have i₂ := eq40 X1 (k X0 X1)
       grind)
    | exact superpose eq40 eq128614
    | (have j0 := eq128614 X0 X1
       grind)
    | exact resolve eq128614 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128614
  have eq128979 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (τ (M.op X1 X1))) ∨ (τ (k X0 X1)) = (τ (k (k X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128885 X0 X1
       have i₂ := eq20303 X1
       grind)
    | exact superpose eq20303 eq128885
    | (have j0 := eq128885 X0 X1
       grind)
    | exact resolve eq128885 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128885
  have eq129056 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (τ (k X0 X1)) = (τ (k (k X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128979 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq128979
    | (have j0 := eq128979 X0 X1
       grind)
    | exact resolve eq128979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128979
  have eq129118 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (k X0 X1) X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq129056 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq129056
    | (have j0 := eq129056 X0 X1
       grind)
    | exact resolve eq129056 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129056
  have eq133387 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (k X0 X1) X1)
       have i₂ := eq129118 X0 X1
       grind)
    | exact superpose eq129118 eq11
    | (have j1 := eq129118 X0 X1
       grind)
    | exact resolve eq11 eq129118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129118
  have eq133618 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133387 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq133387
    | (have j0 := eq133387 X0 X1
       grind)
    | exact resolve eq133387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133387
  have eq144437 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119498 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq119498
    | (have j0 := eq119498 (τ X0) X1
       grind)
    | exact resolve eq119498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144584 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119498 x y
       grind)
    | exact superpose eq119498 eq16
    | (have j1 := eq119498 x y
       grind)
    | exact resolve eq16 eq119498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119498
  have eq145090 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144437 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq144437
    | (have j0 := eq144437 X0 X1
       grind)
    | exact resolve eq144437 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144437
  have eq145237 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145090 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq145090
    | (have j0 := eq145090 X0 X1
       grind)
    | exact resolve eq145090 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq145090
  have eq145442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq144584
       have i₂ := eq126386 x y
       grind)
    | exact superpose eq126386 eq144584
    | (have j1 := eq126386 x y
       grind)
    | (have r₁ := eq144584
       have r₂ := eq126386 x y
       grind)
    | exact resolve eq144584 eq126386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126386
  have eq145443 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144584
       have i₂ := eq686 y x
       grind)
    | exact superpose eq686 eq144584
    | (have j1 := eq686 y x
       grind)
    | (have r₁ := eq144584
       have r₂ := eq686 y x
       grind)
    | exact resolve eq144584 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq144584
  have eq145444 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq145443
  have eq145445 : (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq145442
  have eq145764 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq171 x y
       have i₂ := eq145445
       grind)
    | exact superpose eq145445 eq171
    | (have j0 := eq171 x y
       grind)
    | exact resolve eq171 eq145445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq145445
  have eq145861 : ∀ X0 X1 : G, (σ (M.op X0 (τ (σ X1)))) = (M.op (σ (M.op X0 (τ (σ X1)))) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145237 (σ (M.op X0 (τ (σ X1)))) X1
       have i₂ := eq1367 X0 (σ X1)
       grind)
    | exact superpose eq1367 eq145237
    | exact resolve eq145237 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq145237
  have eq146318 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145861 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145861
    | (have j0 := eq145861 X0 X1
       grind)
    | exact resolve eq145861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145861
  have eq146490 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq146318 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq146318
    | (have j0 := eq146318 X0 X1
       grind)
    | exact resolve eq146318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146318
  have eq160089 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (σ (τ (k (M.op X0 X1) X2))) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (k X0 X1) X2)
       have i₂ := eq124821 X0 X1 X2
       grind)
    | exact superpose eq124821 eq11
    | (have j1 := eq124821 X0 X1 X2
       grind)
    | exact resolve eq11 eq124821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124821
  have eq160337 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160089 X0 X1 X2
       have i₂ := eq11 (k (M.op X0 X1) X2)
       grind)
    | exact superpose eq11 eq160089
    | (have j0 := eq160089 X0 X1 X2
       grind)
    | exact resolve eq160089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160089
  have eq160854 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (k (M.op (k X0 X1) X1) X2) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160337 (k X0 X1) X1 X2
       have i₂ := eq133618 X0 X1
       grind)
    | exact superpose eq133618 eq160337
    | (have j0 := eq160337 X0 X1 X2
       have j1 := eq133618 X0 X1
       grind)
    | exact resolve eq160337 eq133618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133618
  have eq161315 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (k (M.op (k X0 X1) X1) X2) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq160854 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160854
  have eq186833 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1291 X1 (k X0 X1)
       have i₂ := eq161315 X0 X1 X1
       grind)
    | exact superpose eq161315 eq1291
    | (have j1 := eq161315 X0 X1 x
       grind)
    | exact resolve eq1291 eq161315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161315
  have eq187830 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq160337 X0 X1 X1
       have i₂ := eq186833 X0 X1
       grind)
    | exact superpose eq186833 eq160337
    | (have j0 := eq160337 X0 X1 x
       have j1 := eq186833 X0 X1
       grind)
    | exact resolve eq160337 eq186833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160337 eq186833
  have eq187960 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq187830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187830
  have eq188049 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq187960 X0 X1
       have i₂ := eq1291 X1 X0
       grind)
    | exact superpose eq1291 eq187960
    | (have j0 := eq187960 X0 X1
       grind)
    | exact resolve eq187960 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187960
  have eq190086 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (k (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (k X0 X1) X1
       have i₂ := eq188049 X0 X1
       grind)
    | exact superpose eq188049 eq12
    | (have j1 := eq188049 X0 X1
       grind)
    | exact resolve eq12 eq188049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188049
  have eq190633 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq190086 X0 X1
       have j1 := eq118958 X0 X1
       grind)
    | (have r₁ := eq190086 X0 X1
       have r₂ := eq118958 X0 X1
       grind)
    | (have r₁ := eq190086 X0 X0
       have r₂ := eq118958 X0 X0
       grind)
    | exact resolve eq190086 eq118958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118958 eq190086
  have eq191101 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (k X0 (τ X1))) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (k X0 (τ X1))
       have i₂ := eq190633 X0 (τ X1)
       grind)
    | exact superpose eq190633 eq18
    | (have j1 := eq190633 X0 (τ X1)
       grind)
    | exact resolve eq18 eq190633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190633
  have eq191225 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (k (σ X0) X1) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191101 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq191101
    | (have j0 := eq191101 X0 X1
       grind)
    | exact resolve eq191101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq191101
  have eq191501 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (k (σ X0) X1) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191225 X0 X1
       have i₂ := eq20303 X1
       grind)
    | exact superpose eq20303 eq191225
    | (have j0 := eq191225 X0 X1
       grind)
    | exact resolve eq191225 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303 eq191225
  have eq248027 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146490 x y
       have i₂ := eq145444
       grind)
    | exact superpose eq145444 eq146490
    | (have j0 := eq146490 x y
       grind)
    | exact resolve eq146490 eq145444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145444
  have eq248382 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq20277 y
       grind)
    | (have r₁ := eq248027
       have r₂ := eq20277 y
       grind)
    | exact resolve eq248027 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20277 eq248027
  have eq248528 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq248382
       have i₂ := eq20311 y
       grind)
    | exact superpose eq20311 eq248382
    | exact resolve eq248382 eq20311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248382
  have eq258271 : x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1291 y x
       have i₂ := eq248528
       grind)
    | exact superpose eq248528 eq1291
    | exact resolve eq1291 eq248528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248528
  have eq261719 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq172 x y
       have i₂ := eq258271
       grind)
    | exact superpose eq258271 eq172
    | (have j0 := eq172 x y
       grind)
    | exact resolve eq172 eq258271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq258271
  have eq261763 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq261719
  have eq261770 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq261763
       have r₂ := eq145764
       grind)
    | exact resolve eq261763 eq145764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145764 eq261763
  have eq291612 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X1))) = (k (k X0 X1) X1) ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191501 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191501
    | (have j0 := eq191501 (τ X0) X1
       grind)
    | exact resolve eq191501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191501
  have eq292207 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (σ (M.op (τ X0) (τ X1))) = (k (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq291612 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq291612
    | (have j0 := eq291612 X0 X1
       grind)
    | exact resolve eq291612 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq291612
  have eq306590 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X1))) = (k (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq292207 X0 X1
       grind)
    | exact superpose eq292207 eq11
    | (have j1 := eq292207 X0 X1
       grind)
    | exact resolve eq11 eq292207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292207
  have eq306882 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X1))) = (k (k X0 X1) X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306590 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq306590
    | (have j0 := eq306590 X0 X1
       grind)
    | exact resolve eq306590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306590
  have eq309247 : ∀ X0 X1 : G, (k (M.op (σ X0) X1) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306882 (σ X1) X0
       have i₂ := eq118648 X0 X1
       grind)
    | exact superpose eq118648 eq306882
    | (have j0 := eq306882 (σ X0) X1
       have j1 := eq118648 X1 X0
       grind)
    | exact resolve eq306882 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118648 eq306882
  have eq310406 : ∀ X0 X1 : G, (k (M.op (σ X0) X1) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq309247 X0 X1
       have j1 := eq119319 X0 X1
       grind)
    | (have r₁ := eq309247 X0 X1
       have r₂ := eq119319 X0 X1
       grind)
    | (have r₁ := eq309247 X0 (σ X0)
       have r₂ := eq119319 X0 (σ X0)
       grind)
    | exact resolve eq309247 eq119319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119319 eq309247
  have eq310767 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (M.op (σ X0) X1) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310406 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq310406
    | (have j0 := eq310406 X0 X1
       grind)
    | exact resolve eq310406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310406
  have eq310999 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310767 X0 X1
       have i₂ := eq1291 X1 (σ X0)
       grind)
    | exact superpose eq1291 eq310767
    | (have j0 := eq310767 X0 X1
       grind)
    | exact resolve eq310767 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310767
  have eq325303 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq310999 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq310999
    | (have j0 := eq310999 X1 (σ X0)
       grind)
    | exact resolve eq310999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310999
  have eq325936 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq325303 X0 X1
       have i₂ := eq20311 X0
       grind)
    | exact superpose eq20311 eq325303
    | (have j0 := eq325303 X0 X1
       grind)
    | exact resolve eq325303 eq20311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325303
  have eq326028 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq325936 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq325936
    | (have j0 := eq325936 X0 X1
       grind)
    | exact resolve eq325936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325936
  have eq387744 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq326028 y x
       grind)
    | exact superpose eq326028 eq16
    | (have j1 := eq326028 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq326028 y x
       grind)
    | exact resolve eq16 eq326028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326028
  have eq388089 : (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq387744
  have eq390499 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq161
       have i₂ := eq388089
       grind)
    | exact superpose eq388089 eq161
    | exact resolve eq161 eq388089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq390511 : (k x y) = (τ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq388089
       grind)
    | exact superpose eq388089 eq10
    | exact resolve eq10 eq388089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388089
  have eq390898 : (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq390511
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq390511
    | exact resolve eq390511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390511
  have eq390899 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq390499
       have r₂ := eq261770
       grind)
    | exact resolve eq390499 eq261770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261770 eq390499
  have eq391057 : y ≠ (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq958 x y
       have i₂ := eq390898
       grind)
    | exact superpose eq390898 eq958
    | (have j0 := eq958 x y
       grind)
    | exact resolve eq958 eq390898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq391059 : x ≠ (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1101 x y
       have i₂ := eq390898
       grind)
    | exact superpose eq390898 eq1101
    | (have j0 := eq1101 x y
       grind)
    | exact resolve eq1101 eq390898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq403057 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq390899
       grind)
    | exact superpose eq390899 eq16
    | exact resolve eq16 eq390899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403069 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1366 (σ x) y
       have i₂ := eq390899
       grind)
    | exact superpose eq390899 eq1366
    | exact resolve eq1366 eq390899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403160 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq390899
  have eq403193 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq403069
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq403069
    | exact resolve eq403069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403069
  have eq403223 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq403193
       have i₂ := eq19904 y
       grind)
    | exact superpose eq19904 eq403193
    | exact resolve eq403193 eq19904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19904 eq403193
  have eq404868 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq403223
       grind)
    | exact superpose eq403223 eq16
    | exact resolve eq16 eq403223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404880 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1366 (σ x) y
       have i₂ := eq403223
       grind)
    | exact superpose eq403223 eq1366
    | exact resolve eq1366 eq403223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq403223
  have eq405001 : x = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq404880
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq404880
    | exact resolve eq404880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404880
  have eq405031 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq405001
       have i₂ := eq390898
       grind)
    | exact superpose eq390898 eq405001
    | exact resolve eq405001 eq390898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405001
  have eq405055 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq391057
       have i₂ := eq405031
       grind)
    | exact superpose eq405031 eq391057
    | (have r₁ := eq391057
       have r₂ := eq405031
       grind)
    | exact resolve eq391057 eq405031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391057 eq405031
  have eq405278 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq405055
  have eq405299 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq405278
       have r₂ := eq391059
       grind)
    | exact resolve eq405278 eq391059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391059 eq405278
  have eq406420 : x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285 y x
       have i₂ := eq405299
       grind)
    | exact superpose eq405299 eq1285
    | exact resolve eq1285 eq405299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq409452 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq404868
       have i₂ := eq406420
       grind)
    | exact superpose eq406420 eq404868
    | exact resolve eq404868 eq406420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404868 eq406420
  have eq409453 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by grind
  clear eq409452
  have eq409454 : y = (M.op y y) := by grind
  clear eq409453
  have eq495057 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq403057
       have i₂ := eq405299
       grind)
    | exact superpose eq405299 eq403057
    | exact resolve eq403057 eq405299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403057 eq405299
  have eq495063 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq495057
  have eq497730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq146490 x y
       have i₂ := eq495063
       grind)
    | exact superpose eq495063 eq146490
    | exact resolve eq146490 eq495063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146490 eq495063
  have eq497736 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq497730
  have eq497745 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq497736
       have i₂ := eq409454
       grind)
    | exact superpose eq409454 eq497736
    | exact resolve eq497736 eq409454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497736
  have eq497760 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq497745
       have r₂ := eq403160
       grind)
    | exact resolve eq497745 eq403160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403160 eq497745
  have eq497845 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1291 (σ y) (σ x)
       have i₂ := eq497760
       grind)
    | exact superpose eq497760 eq1291
    | exact resolve eq1291 eq497760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq497760
  have eq497908 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq497845
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq497845
    | exact resolve eq497845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497845
  have eq497958 : (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq497908
       have i₂ := eq390898
       grind)
    | exact superpose eq390898 eq497908
    | exact resolve eq497908 eq390898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390898 eq497908
  have eq497989 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq497958
       have i₂ := eq409454
       grind)
    | exact superpose eq409454 eq497958
    | exact resolve eq497958 eq409454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409454 eq497958
  have eq500325 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq497989
       grind)
    | exact superpose eq497989 eq10
    | exact resolve eq10 eq497989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497989
  have eq500940 : x = y := by
    first
    | (have i₁ := eq500325
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq500325
    | exact resolve eq500325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500325
  have eq503470 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq500940
       grind)
    | exact superpose eq500940 eq16
    | exact resolve eq16 eq500940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500940
  have eq503598 : False := by grind
  exact eq503598

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq487 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq487
    | (have j0 := eq487 (σ X0) (σ X1)
       grind)
    | exact resolve eq487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq487 X0 X1
       grind)
    | exact superpose eq487 eq493
    | (have j0 := eq493 X0 X1
       have j1 := eq487 (σ X0) (σ X1)
       grind)
    | exact resolve eq493 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2597 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq914 x y
       grind)
    | exact superpose eq914 eq16
    | (have j1 := eq914 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq914 x y
       grind)
    | exact resolve eq16 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq2618 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2597
  have eq2633 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2618
       grind)
    | exact superpose eq2618 eq16
    | exact resolve eq16 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2636 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2618
       grind)
    | exact superpose eq2618 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2618
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2618
       grind)
    | exact resolve eq13 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2637 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq2618
       grind)
    | exact superpose eq2618 eq12
    | exact resolve eq12 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618
  have eq2638 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2636
  have eq2640 : (σ y) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2637
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2637
    | exact resolve eq2637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2641 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2638
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2638
    | exact resolve eq2638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2642 : (σ (M.op x y)) = (σ y) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq487 eq2640
    | (have j1 := eq487 x y
       grind)
    | exact resolve eq2640 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq2643 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq487 eq2641
    | (have j1 := eq487 x y
       grind)
    | exact resolve eq2641 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq2641
  have eq2645 : y = (M.op x y) := by grind
  clear eq2633 eq2642 eq2643
  have eq2647 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq16
    | exact resolve eq16 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2650 : y ≠ y ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2645
       grind)
    | exact resolve eq13 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2651 : x ≠ y ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq12
    | exact resolve eq12 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2652 : x = y ∨ y = (k x y) := by grind
  clear eq2650
  have eq2653 : y = (k x y) := by
    first
    | (have r₁ := eq2652
       have r₂ := eq2651
       grind)
    | exact resolve eq2652 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq2652
  have eq2659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq493 x y
       have i₂ := eq2653
       grind)
    | exact superpose eq2653 eq493
    | (have j0 := eq493 x y
       grind)
    | exact resolve eq493 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq2653
  have eq2662 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2659
  have eq2667 : False := by grind
  exact eq2667

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq21 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq31 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq43
    | exact resolve eq43 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq43 x x
       grind)
    | exact superpose eq43 eq21
    | (have j1 := eq43 X0 X0
       grind)
    | exact resolve eq21 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43
  have eq189 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq396 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq409 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq396 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq396
    | (have j0 := eq396 X0
       grind)
    | exact resolve eq396 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq396
  have eq413 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq409 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq409
    | (have j0 := eq409 X0
       grind)
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq433 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq12
    | (have j1 := eq413 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq413 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq413 X0
       grind)
    | exact resolve eq12 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq434 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq433 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq444 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq434 X0
       grind)
    | exact superpose eq434 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq434 X0
       grind)
    | exact resolve eq14 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq449 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq456 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq449 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq449 x
       have r₂ := eq12 (k x x) x
       grind)
    | (have r₁ := eq449 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq449 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq907 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (M.op (τ X0) X1) X2
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq38
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq38 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq44
  have eq922 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq907 X0 X1 X2
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq907
    | (have j0 := eq907 X0 X1 X2
       grind)
    | exact resolve eq907 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq907
  have eq1062 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq456 X0
       grind)
    | exact superpose eq456 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq456 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq456 X0
       grind)
    | exact resolve eq12 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1081 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1118 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq110 x X2 X0 X1
       grind)
    | exact superpose eq110 eq31
    | exact resolve eq31 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1119 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq110 x X2 X0 X1
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1201 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1119 x X1 X0
       grind)
    | exact superpose eq1119 eq9
    | exact resolve eq9 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1206 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1119 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1119 eq9
    | exact resolve eq9 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1119 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1119 eq1118
    | exact resolve eq1118 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq6034 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1119 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1206 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1206 eq1119
    | exact resolve eq1119 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq1206
  have eq6113 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq6034 X0 X1 X2
       grind)
    | exact superpose eq6034 eq88
    | exact resolve eq88 eq6034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq6034
  have eq6622 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X2 (M.op X3 (τ X0))))
       have i₂ := eq6113 (τ X0) X2 X3 X1
       grind)
    | exact superpose eq6113 eq18
    | exact resolve eq18 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6635 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6622 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6622
    | exact resolve eq6622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6622
  have eq22886 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1081 (τ X0)
       have i₂ := eq922 X0 (τ X0) X0
       grind)
    | exact superpose eq922 eq1081
    | (have j0 := eq1081 (τ X0)
       have j1 := eq922 X0 (τ X0) x
       grind)
    | exact resolve eq1081 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq1081
  have eq22946 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22886
  have eq23002 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22946 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq22946 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq22946 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22946
  have eq23051 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23002 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq23002
    | (have j0 := eq23002 X0
       grind)
    | exact resolve eq23002 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23002
  have eq23079 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23051 X0
       have i₂ := eq30 (τ X0)
       grind)
    | exact superpose eq30 eq23051
    | (have j0 := eq23051 X0
       grind)
    | exact resolve eq23051 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23051
  have eq23089 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23079 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq23079
    | (have j0 := eq23079 X0
       grind)
    | exact resolve eq23079 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq23079
  have eq23090 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq23089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23089
  have eq23099 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23090 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23090
    | exact resolve eq23090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23140 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (k X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6635 X0 X1 X2 (τ X0)
       have i₂ := eq23090 X0
       grind)
    | exact superpose eq23090 eq6635
    | exact resolve eq6635 eq23090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6635
  have eq23199 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6113 (τ X0) X2 (τ X0) X1
       have i₂ := eq23090 X0
       grind)
    | exact superpose eq23090 eq6113
    | exact resolve eq6113 eq23090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq23257 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq23099 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq23099
    | exact resolve eq23099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23099
  have eq23276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23257 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23257
    | exact resolve eq23257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23257
  have eq23394 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23276 (σ X0)
       grind)
    | exact superpose eq23276 eq15
    | exact resolve eq15 eq23276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23453 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23394 X0
       have i₂ := eq23276 X0
       grind)
    | exact superpose eq23276 eq23394
    | exact resolve eq23394 eq23276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23394
  have eq24092 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1201 (σ X0) (σ X0)
       have i₂ := eq23453 X0
       grind)
    | exact superpose eq23453 eq1201
    | exact resolve eq1201 eq23453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26445 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X3)) = X0 ∨ (M.op (σ X3) (σ X3)) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq170 X0 (M.op X1 (M.op X2 (τ (k X0 X0)))) X2
       have i₂ := eq23140 X0 X1 X2
       grind)
    | exact superpose eq23140 eq170
    | exact resolve eq170 eq23140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq23140
  have eq26534 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26445 X0 X1 X2 X3
       have i₂ := eq23453 X3
       grind)
    | exact superpose eq23453 eq26445
    | (have j0 := eq26445 X0 X1 X2 X3
       grind)
    | exact resolve eq26445 eq23453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23453 eq26445
  have eq26612 : ∀ X0 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq26534 X0 x x X3
       have i₂ := eq23199 X0 x x
       grind)
    | exact superpose eq23199 eq26534
    | (have j0 := eq26534 X0 x x X3
       grind)
    | exact resolve eq26534 eq23199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23199 eq26534
  have eq26674 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq26612 X0 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq26612
    | (have j0 := eq26612 X0 X3
       grind)
    | exact resolve eq26612 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26612
  have eq26723 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 := by
    intro X0 X3
    first
    | (have j0 := eq26674 X0 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq26674 (M.op (σ (M.op X3 X3)) x) X3
       have r₂ := eq12 (σ (M.op X3 X3)) x
       grind)
    | (have r₁ := eq26674 X0 X3
       have r₂ := eq12 X0 (σ X3)
       grind)
    | exact resolve eq26674 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26674
  have eq31149 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26723 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26723
    | (have j0 := eq26723 X1 (τ X0)
       grind)
    | exact resolve eq26723 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq26723 (σ X0) X1
       grind)
    | exact superpose eq26723 eq15
    | (have j1 := eq26723 (σ X0) X1
       grind)
    | exact resolve eq15 eq26723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26723
  have eq31457 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31149 X0 X1
       have i₂ := eq23090 X0
       grind)
    | exact superpose eq23090 eq31149
    | (have j0 := eq31149 X0 X1
       grind)
    | exact resolve eq31149 eq23090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23090 eq31149
  have eq31506 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31457 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq31457
    | (have j0 := eq31457 X0 X1
       grind)
    | exact resolve eq31457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31457
  have eq31523 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31506 X0 X1
       have i₂ := eq23276 X0
       grind)
    | exact superpose eq23276 eq31506
    | (have j0 := eq31506 X0 X1
       grind)
    | exact resolve eq31506 eq23276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23276 eq31506
  have eq31808 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq31523 X1 (τ X0)
       grind)
    | exact superpose eq31523 eq18
    | (have j1 := eq31523 X1 (τ X0)
       grind)
    | exact resolve eq18 eq31523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31523
  have eq39889 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31808 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31808
    | exact resolve eq31808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31808
  have eq40178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39889 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39889
    | (have j0 := eq39889 X0 X1
       grind)
    | exact resolve eq39889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39889
  have eq50127 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31310 x y
       grind)
    | exact superpose eq31310 eq16
    | (have j1 := eq31310 x y
       grind)
    | exact resolve eq16 eq31310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31310
  have eq51121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50127
       have i₂ := eq40178 x y
       grind)
    | exact superpose eq40178 eq50127
    | (have j1 := eq40178 x y
       grind)
    | (have r₁ := eq50127
       have r₂ := eq40178 x y
       grind)
    | exact resolve eq50127 eq40178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40178
  have eq51124 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq51121
  have eq51195 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1201 y y
       have i₂ := eq51124
       grind)
    | exact superpose eq51124 eq1201
    | exact resolve eq1201 eq51124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51200 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1207 y y
       have i₂ := eq51124
       grind)
    | exact superpose eq51124 eq1207
    | exact resolve eq1207 eq51124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq51124
  have eq51888 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq50127
       have i₂ := eq51200
       grind)
    | exact superpose eq51200 eq50127
    | exact resolve eq50127 eq51200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50127 eq51200
  have eq51909 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq51888
  have eq52443 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51909
       have i₂ := eq51195
       grind)
    | exact superpose eq51195 eq51909
    | exact resolve eq51909 eq51195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51195 eq51909
  have eq52446 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq52443
  have eq52447 : (σ x) = (σ (M.op y y)) := by grind
  clear eq52446
  have eq52458 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24092 y
       have i₂ := eq52447
       grind)
    | exact superpose eq52447 eq24092
    | exact resolve eq24092 eq52447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24092
  have eq52465 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq52447
       grind)
    | exact superpose eq52447 eq10
    | exact resolve eq10 eq52447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52447
  have eq52617 : x = (M.op y y) := by
    first
    | (have i₁ := eq52465
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52465
    | exact resolve eq52465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52465
  have eq53243 : x = (M.op x y) := by
    first
    | (have i₁ := eq1201 y y
       have i₂ := eq52617
       grind)
    | exact superpose eq52617 eq1201
    | exact resolve eq1201 eq52617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq52617
  have eq53980 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52458
       grind)
    | exact superpose eq52458 eq16
    | exact resolve eq16 eq52458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52458
  have eq54046 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq53980
       have i₂ := eq53243
       grind)
    | exact superpose eq53243 eq53980
    | exact resolve eq53980 eq53243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53243 eq53980
  have eq54047 : False := by grind
  exact eq54047

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq21 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq31 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq155 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq43
    | exact resolve eq43 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq43 x x
       grind)
    | exact superpose eq43 eq21
    | (have j1 := eq43 X0 X0
       grind)
    | exact resolve eq21 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43
  have eq174 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq380 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq393 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq380 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq380
    | (have j0 := eq380 X0
       grind)
    | exact resolve eq380 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq380
  have eq397 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq393
    | (have j0 := eq393 X0
       grind)
    | exact resolve eq393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq417 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq12
    | (have j1 := eq397 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq397 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq397 X0
       grind)
    | exact resolve eq12 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq418 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq428 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq418 X0
       grind)
    | exact superpose eq418 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq418 X0
       grind)
    | exact resolve eq14 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq433 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq440 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq433 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq433 x
       have r₂ := eq12 (k x x) x
       grind)
    | (have r₁ := eq433 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq433 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq893 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (M.op (τ X0) X1) X2
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq38
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq38 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq44
  have eq908 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq893 X0 X1 X2
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq893
    | (have j0 := eq893 X0 X1 X2
       grind)
    | exact resolve eq893 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq893
  have eq1048 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 (k X0 X0) X0
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq440 X0
       grind)
    | (have r₁ := eq12 (k X0 X0) X0
       have r₂ := eq440 X0
       grind)
    | exact resolve eq12 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq1067 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1048 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1099 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq99 x X2 X0 X1
       grind)
    | exact superpose eq99 eq31
    | exact resolve eq31 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1100 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq99 x X2 X0 X1
       grind)
    | exact superpose eq99 eq9
    | exact resolve eq9 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1176 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1100 x X1 X0
       grind)
    | exact superpose eq1100 eq9
    | exact resolve eq9 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1100 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1100 eq9
    | exact resolve eq9 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1099 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1100 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1100 eq1099
    | exact resolve eq1099 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq5974 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1100 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1181 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1181 eq1100
    | exact resolve eq1100 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq1181
  have eq6050 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq82 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq5974 X0 X1 X2
       grind)
    | exact superpose eq5974 eq82
    | exact resolve eq82 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq5974
  have eq6554 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X2 (M.op X3 (τ X0))))
       have i₂ := eq6050 (τ X0) X2 X3 X1
       grind)
    | exact superpose eq6050 eq18
    | exact resolve eq18 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6567 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6554 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6554
    | exact resolve eq6554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6554
  have eq22661 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1067 (τ X0)
       have i₂ := eq908 X0 (τ X0) X0
       grind)
    | exact superpose eq908 eq1067
    | (have j0 := eq1067 (τ X0)
       have j1 := eq908 X0 (τ X0) x
       grind)
    | exact resolve eq1067 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq1067
  have eq22719 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22661
  have eq22775 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22719 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq22719 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq22719 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22719
  have eq22824 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22775 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq22775
    | (have j0 := eq22775 X0
       grind)
    | exact resolve eq22775 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22775
  have eq22852 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22824 X0
       have i₂ := eq30 (τ X0)
       grind)
    | exact superpose eq30 eq22824
    | (have j0 := eq22824 X0
       grind)
    | exact resolve eq22824 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22824
  have eq22862 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22852 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq22852
    | (have j0 := eq22852 X0
       grind)
    | exact resolve eq22852 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq22852
  have eq22863 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq22862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22862
  have eq22872 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22863 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22863
    | exact resolve eq22863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22913 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (k X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6567 X0 X1 X2 (τ X0)
       have i₂ := eq22863 X0
       grind)
    | exact superpose eq22863 eq6567
    | exact resolve eq6567 eq22863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6567
  have eq22972 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6050 (τ X0) X2 (τ X0) X1
       have i₂ := eq22863 X0
       grind)
    | exact superpose eq22863 eq6050
    | exact resolve eq6050 eq22863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq23030 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22872 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq22872
    | exact resolve eq22872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22872
  have eq23049 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23030 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23030
    | exact resolve eq23030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23030
  have eq23169 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23049 (σ X0)
       grind)
    | exact superpose eq23049 eq15
    | exact resolve eq15 eq23049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23228 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23169 X0
       have i₂ := eq23049 X0
       grind)
    | exact superpose eq23049 eq23169
    | exact resolve eq23169 eq23049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23169
  have eq23870 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1176 (σ X0) (σ X0)
       have i₂ := eq23228 X0
       grind)
    | exact superpose eq23228 eq1176
    | exact resolve eq1176 eq23228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26134 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X3)) = X0 ∨ (M.op (σ X3) (σ X3)) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq155 X0 (M.op X1 (M.op X2 (τ (k X0 X0)))) X2
       have i₂ := eq22913 X0 X1 X2
       grind)
    | exact superpose eq22913 eq155
    | exact resolve eq155 eq22913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq22913
  have eq26223 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (M.op X1 (M.op X2 (τ (k X0 X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26134 X0 X1 X2 X3
       have i₂ := eq23228 X3
       grind)
    | exact superpose eq23228 eq26134
    | (have j0 := eq26134 X0 X1 X2 X3
       grind)
    | exact resolve eq26134 eq23228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23228 eq26134
  have eq26300 : ∀ X0 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq26223 X0 x x X3
       have i₂ := eq22972 X0 x x
       grind)
    | exact superpose eq22972 eq26223
    | (have j0 := eq26223 X0 x x X3
       grind)
    | exact resolve eq26223 eq22972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22972 eq26223
  have eq26361 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq26300 X0 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq26300
    | (have j0 := eq26300 X0 X3
       grind)
    | exact resolve eq26300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26300
  have eq26410 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (σ (M.op X3 X3)) = X0 := by
    intro X0 X3
    first
    | (have j0 := eq26361 X0 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq26361 (M.op (σ (M.op X3 X3)) x) X3
       have r₂ := eq12 (σ (M.op X3 X3)) x
       grind)
    | (have r₁ := eq26361 X0 X3
       have r₂ := eq12 X0 (σ X3)
       grind)
    | exact resolve eq26361 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26361
  have eq31014 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26410 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26410
    | (have j0 := eq26410 X1 (τ X0)
       grind)
    | exact resolve eq26410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq26410 (σ X0) X1
       grind)
    | exact superpose eq26410 eq15
    | (have j1 := eq26410 (σ X0) X1
       grind)
    | exact resolve eq15 eq26410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26410
  have eq31327 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31014 X0 X1
       have i₂ := eq22863 X0
       grind)
    | exact superpose eq22863 eq31014
    | (have j0 := eq31014 X0 X1
       grind)
    | exact resolve eq31014 eq22863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22863 eq31014
  have eq31377 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31327 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq31327
    | (have j0 := eq31327 X0 X1
       grind)
    | exact resolve eq31327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31327
  have eq31395 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31377 X0 X1
       have i₂ := eq23049 X0
       grind)
    | exact superpose eq23049 eq31377
    | (have j0 := eq31377 X0 X1
       grind)
    | exact resolve eq31377 eq23049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23049 eq31377
  have eq31685 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq31395 X1 (τ X0)
       grind)
    | exact superpose eq31395 eq18
    | (have j1 := eq31395 X1 (τ X0)
       grind)
    | exact resolve eq18 eq31395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31395
  have eq39714 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31685 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31685
    | exact resolve eq31685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31685
  have eq40007 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39714 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39714
    | (have j0 := eq39714 X0 X1
       grind)
    | exact resolve eq39714 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39714
  have eq50063 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31178 x y
       grind)
    | exact superpose eq31178 eq16
    | (have j1 := eq31178 x y
       grind)
    | exact resolve eq16 eq31178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31178
  have eq50914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50063
       have i₂ := eq40007 x y
       grind)
    | exact superpose eq40007 eq50063
    | (have j1 := eq40007 x y
       grind)
    | (have r₁ := eq50063
       have r₂ := eq40007 x y
       grind)
    | exact resolve eq50063 eq40007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40007
  have eq50917 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq50914
  have eq50988 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1176 y y
       have i₂ := eq50917
       grind)
    | exact superpose eq50917 eq1176
    | exact resolve eq1176 eq50917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50993 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1182 y y
       have i₂ := eq50917
       grind)
    | exact superpose eq50917 eq1182
    | exact resolve eq1182 eq50917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq50917
  have eq51567 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq50063
       have i₂ := eq50993
       grind)
    | exact superpose eq50993 eq50063
    | exact resolve eq50063 eq50993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50063 eq50993
  have eq51588 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq51567
  have eq52221 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51588
       have i₂ := eq50988
       grind)
    | exact superpose eq50988 eq51588
    | exact resolve eq51588 eq50988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50988 eq51588
  have eq52224 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq52221
  have eq52225 : (σ x) = (σ (M.op y y)) := by grind
  clear eq52224
  have eq52236 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23870 y
       have i₂ := eq52225
       grind)
    | exact superpose eq52225 eq23870
    | exact resolve eq23870 eq52225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23870
  have eq52243 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq52225
       grind)
    | exact superpose eq52225 eq10
    | exact resolve eq10 eq52225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52225
  have eq52393 : x = (M.op y y) := by
    first
    | (have i₁ := eq52243
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52243
    | exact resolve eq52243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52243
  have eq53029 : x = (M.op x y) := by
    first
    | (have i₁ := eq1176 y y
       have i₂ := eq52393
       grind)
    | exact superpose eq52393 eq1176
    | exact resolve eq1176 eq52393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq52393
  have eq53180 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52236
       grind)
    | exact superpose eq52236 eq16
    | exact resolve eq16 eq52236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52236
  have eq53246 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq53180
       have i₂ := eq53029
       grind)
    | exact superpose eq53029 eq53180
    | exact resolve eq53180 eq53029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53029 eq53180
  have eq53247 : False := by grind
  exact eq53247
