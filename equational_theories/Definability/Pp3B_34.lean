import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq514 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq525 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq14
    | exact resolve eq14 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq525
    | exact resolve eq525 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq525
    | exact resolve eq525 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4154 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op (M.op (M.op x (M.op x y)) X0) (M.op (M.op x y) X1)) (M.op (M.op x (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq514 sF0 (M.op (M.op x sF0) x) x
       have i₂ := eq14 sF0 (M.op x sF0) x
       grind)
    | exact superpose eq14 eq514
    | exact resolve eq514 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq4168 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq875 eq4154
    | exact resolve eq4154 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq4154
  have eq6277 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq6298 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6277
  have eq6301 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6298
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq6298
    | exact resolve eq6298 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6298
  have eq6324 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6301
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6301 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301
  have eq6345 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6324 eq87
    | exact resolve eq87 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq10923 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6324 eq109
    | exact resolve eq109 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq23628 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq10923
       grind)
    | exact superpose eq10923 eq16
    | exact resolve eq16 eq10923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10923
  have eq23687 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6345 eq23628
    | exact resolve eq23628 eq6345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23628
  have eq23691 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23687
       have r₂ := eq13 y y
       grind)
    | exact resolve eq23687 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23687
  have eq23692 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq23691
       grind)
    | exact superpose eq23691 eq76
    | exact resolve eq76 eq23691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq23732 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6324 eq23692
    | exact resolve eq23692 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324 eq23692
  have eq36426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq36436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq36426
    | exact resolve eq36426 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36426
  have eq36447 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq36436
       have r₂ := eq28
       grind)
    | exact resolve eq36436 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36436
  have eq36498 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36447 eq873
    | exact resolve eq873 eq36447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36447
  have eq36536 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36498 eq6345
    | exact resolve eq6345 eq36498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36498
  have eq36639 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq36536
       have i₂ := eq23691
       grind)
    | exact superpose eq23691 eq36536
    | exact resolve eq36536 eq23691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36536
  have eq36655 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq36639
    | exact resolve eq36639 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36639
  have eq37193 : (τ (σ x)) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq36655 eq6345
    | exact resolve eq6345 eq36655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345 eq36655
  have eq37273 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq37193
       have i₂ := eq23691
       grind)
    | exact superpose eq23691 eq37193
    | exact resolve eq37193 eq23691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23691 eq37193
  have eq37282 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq37273
    | exact resolve eq37273 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37273
  have eq37283 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq37282
  have eq37781 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq525 y X0
       have i₂ := eq37283
       grind)
    | exact superpose eq37283 eq525
    | exact resolve eq525 eq37283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37785 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq37283
       grind)
    | exact superpose eq37283 eq14
    | exact resolve eq14 eq37283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37283
  have eq37860 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq37785 X0
       have i₂ := eq873 y X0
       grind)
    | exact superpose eq873 eq37785
    | exact resolve eq37785 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37785
  have eq38177 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq37781 X0
       have i₂ := eq37860 X0
       grind)
    | exact superpose eq37860 eq37781
    | exact resolve eq37781 eq37860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37781 eq37860
  have eq38257 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq38177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38177
  have eq38430 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq873 y x
       have i₂ := eq38257 X0
       grind)
    | exact superpose eq38257 eq873
    | (have j1 := eq38257 y
       grind)
    | exact resolve eq873 eq38257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38257
  have eq38652 : y ≠ y ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq38430 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38430
  have eq38653 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq38652
  have eq38777 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq525 y X0
       have i₂ := eq38653
       grind)
    | exact superpose eq38653 eq525
    | exact resolve eq525 eq38653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38781 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq38653
       grind)
    | exact superpose eq38653 eq14
    | exact resolve eq14 eq38653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38653
  have eq38856 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38781 X0
       have i₂ := eq873 y X0
       grind)
    | exact superpose eq873 eq38781
    | exact resolve eq38781 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38781
  have eq39367 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38777 X0
       have i₂ := eq38856 X0
       grind)
    | exact superpose eq38856 eq38777
    | exact resolve eq38777 eq38856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38777
  have eq39454 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq39367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39367
  have eq39620 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23732
       have i₂ := eq39454 X0
       grind)
    | exact superpose eq39454 eq23732
    | (have j1 := eq39454 X0
       grind)
    | exact resolve eq23732 eq39454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39678 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq873 y y
       have i₂ := eq39454 X0
       grind)
    | exact superpose eq39454 eq873
    | (have j1 := eq39454 x
       grind)
    | exact resolve eq873 eq39454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq39454
  have eq39689 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39620 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39620
    | (have j0 := eq39620 X0
       grind)
    | exact resolve eq39620 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39620
  have eq40312 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq39678 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39678
  have eq40313 : x = (M.op y x) := by grind
  clear eq40312
  have eq40382 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38856 x
       have i₂ := eq40313
       grind)
    | exact superpose eq40313 eq38856
    | exact resolve eq38856 eq40313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38856 eq40313
  have eq40438 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40382
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40382
    | exact resolve eq40382 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40382
  have eq40460 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq517 y
       have i₂ := eq40438
       grind)
    | exact superpose eq40438 eq517
    | exact resolve eq517 eq40438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40438
  have eq40527 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40460
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40460
    | exact resolve eq40460 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq40460
  have eq40528 : y = (M.op x y) := by grind
  clear eq40527
  have eq40546 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq40528 eq21
    | exact resolve eq21 eq40528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq40742 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40546
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40546
    | exact resolve eq40546 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40546
  have eq40921 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq40742 eq27
    | exact resolve eq27 eq40742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq43416 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq40742 eq39689
    | (have j0 := eq39689 X0
       grind)
    | exact resolve eq39689 eq40742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39689
  have eq43428 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq517 X0
       have i₂ := eq43416 (M.op X0 X0)
       grind)
    | exact superpose eq43416 eq517
    | (have j1 := eq43416 X0
       grind)
    | exact resolve eq517 eq43416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq43416
  have eq43490 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq40921 eq43428
    | (have j0 := eq43428 X0
       grind)
    | exact resolve eq43428 eq40921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43428
  have eq43501 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq43490 X0
       grind)
    | (have r₁ := eq43490 X0
       have r₂ := eq28
       grind)
    | exact resolve eq43490 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43490
  have eq43552 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23732
       have i₂ := eq43501 y
       grind)
    | exact superpose eq43501 eq23732
    | exact resolve eq23732 eq43501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23732
  have eq43755 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40742 eq43552
    | exact resolve eq43552 eq40742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43552
  have eq43815 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43755
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq43755
    | exact resolve eq43755 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq43755
  have eq43850 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40742 eq43815
    | exact resolve eq43815 eq40742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40742 eq43815
  have eq44681 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq43850 eq525
    | exact resolve eq525 eq43850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq43850
  have eq44812 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op y X0) (M.op y X1)) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq40528 eq4168
    | exact resolve eq4168 eq40528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168 eq40528
  have eq44813 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44812 X0 X1
       have i₂ := eq43501 X0
       grind)
    | exact superpose eq43501 eq44812
    | exact resolve eq44812 eq43501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44812
  have eq44814 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44813 X0 X1
       have i₂ := eq43501 X1
       grind)
    | exact superpose eq43501 eq44813
    | exact resolve eq44813 eq43501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43501 eq44813
  have eq51150 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44681 x
       have i₂ := eq44814 sF1 x
       grind)
    | exact superpose eq44814 eq44681
    | exact resolve eq44681 eq44814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44681
  have eq51229 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51150 eq44814
    | exact resolve eq44814 eq51150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44814 eq51150
  have eq52813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51229 eq40921
    | exact resolve eq40921 eq51229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40921 eq51229
  have eq52859 : False := by grind
  exact eq52859

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq61 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq419 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq426 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq419 X0
       grind)
    | exact superpose eq419 eq14
    | exact resolve eq14 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq684 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq14
    | (have j1 := eq83 X0 X1
       grind)
    | exact resolve eq14 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq899 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq426
    | exact resolve eq426 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq60 eq426
    | exact resolve eq426 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq904 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq61 eq426
    | exact resolve eq426 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq8206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8206
    | exact resolve eq8206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8206
  have eq8218 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8207
       have r₂ := eq28
       grind)
    | exact resolve eq8207 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207
  have eq8220 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8218
    | exact resolve eq8218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8218
  have eq8374 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq8393 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8220 eq899
    | exact resolve eq899 eq8220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8220
  have eq8394 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8393
    | exact resolve eq8393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8393
  have eq8396 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8374
    | exact resolve eq8374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8374
  have eq8397 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq8396
  have eq8421 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8394
  have eq8443 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8421
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8421
    | exact resolve eq8421 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8421
  have eq8444 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8443
  have eq8652 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq8444
       grind)
    | exact superpose eq8444 eq75
    | exact resolve eq75 eq8444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8444
  have eq8671 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8652
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8652
    | exact resolve eq8652 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8652
  have eq8688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8671 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8671
  have eq8689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8688
  have eq8694 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8689
    | exact resolve eq8689 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8689
  have eq8695 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8694
  have eq8748 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8695 eq899
    | exact resolve eq899 eq8695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8695
  have eq8749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8748
    | exact resolve eq8748 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8748
  have eq8750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8749
  have eq8882 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8750 eq28
    | exact resolve eq28 eq8750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8750
  have eq9855 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8397 eq100
    | exact resolve eq100 eq8397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq8397
  have eq9866 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9855
  have eq9928 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq899 x x
       have i₂ := eq9866
       grind)
    | exact superpose eq9866 eq899
    | exact resolve eq899 eq9866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9866
  have eq9929 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9928
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9928
    | exact resolve eq9928 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9928
  have eq9937 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9929 eq52
    | (have r₁ := eq52
       have r₂ := eq9929
       grind)
    | exact resolve eq52 eq9929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9929
  have eq9970 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq9937
  have eq10883 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9970 eq82
    | exact resolve eq82 eq9970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq10907 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq10883
    | exact resolve eq10883 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10883
  have eq10912 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10907
       have r₂ := eq51
       grind)
    | exact resolve eq10907 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10907
  have eq10926 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10912
       grind)
    | exact superpose eq10912 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10912
  have eq10929 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10926
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10926
    | exact resolve eq10926 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10926
  have eq10930 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq10929
  have eq10940 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10930
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10930
    | exact resolve eq10930 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10930
  have eq12118 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq899 x x
       have i₂ := eq10940
       grind)
    | exact superpose eq10940 eq899
    | exact resolve eq899 eq10940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq10940
  have eq12119 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12118
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12118
    | exact resolve eq12118 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118
  have eq12120 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12119
  have eq12253 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12120 eq29
    | exact resolve eq29 eq12120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12120
  have eq12400 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq12253
    | exact resolve eq12253 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12253
  have eq12401 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12400
  have eq12402 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12401 eq21
    | exact resolve eq21 eq12401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12401
  have eq12541 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12402
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12402
    | exact resolve eq12402 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12402
  have eq12633 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12541 eq8882
    | (have r₁ := eq8882
       have r₂ := eq12541
       grind)
    | exact resolve eq8882 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8882
  have eq12651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12633
  have eq12652 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12651
  have eq12714 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12652 eq52
    | (have r₁ := eq52
       have r₂ := eq12652
       grind)
    | exact resolve eq52 eq12652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq12717 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12652 eq216
    | exact resolve eq216 eq12652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq12743 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12652 eq904
    | exact resolve eq904 eq12652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq12652
  have eq12751 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12714
  have eq13018 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12751 eq82
    | exact resolve eq82 eq12751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq12751
  have eq13049 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq13018
    | exact resolve eq13018 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13018
  have eq13055 : y = (k y x) := by
    first
    | (have r₁ := eq13049
       have r₂ := eq51
       grind)
    | exact resolve eq13049 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13049
  have eq13080 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq13055
       grind)
    | exact superpose eq13055 eq75
    | exact resolve eq75 eq13055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13055
  have eq13101 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13080
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13080
    | exact resolve eq13080 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13080
  have eq14558 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (k (σ y) (σ x))) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq684 y x X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq684
    | (have j0 := eq684 y x x
       grind)
    | exact resolve eq684 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq684
  have eq14646 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13101 eq14558
    | exact resolve eq14558 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101 eq14558
  have eq14761 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14646 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14646
    | (have j0 := eq14646 X0
       grind)
    | exact resolve eq14646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14646
  have eq14870 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14761 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14761
    | (have j0 := eq14761 X0
       grind)
    | exact resolve eq14761 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14761
  have eq14972 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14870 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14870
    | (have j0 := eq14870 X0
       grind)
    | exact resolve eq14870 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14870
  have eq15072 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14972 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14972
    | (have j0 := eq14972 X0
       grind)
    | exact resolve eq14972 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14972
  have eq15147 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15072 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15072
    | (have j0 := eq15072 X0
       grind)
    | exact resolve eq15072 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15172 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq15147
    | (have j0 := eq15147 X0
       grind)
    | exact resolve eq15147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147
  have eq24177 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12743 eq12717
    | exact resolve eq12717 eq12743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12717 eq12743
  have eq24239 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24177
  have eq24243 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq24239
    | exact resolve eq24239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24239
  have eq25298 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24243 eq28
    | exact resolve eq28 eq24243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24243
  have eq25363 : x = (M.op x y) := by
    first
    | (have r₁ := eq25298
       have r₂ := eq12541
       grind)
    | exact resolve eq25298 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541 eq25298
  have eq25365 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25363 eq21
    | exact resolve eq21 eq25363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq25449 : x = (M.op x x) := by
    first
    | exact superpose eq25363 eq902
    | exact resolve eq902 eq25363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq25520 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25365
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25365
    | exact resolve eq25365 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25365
  have eq25553 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq25520 eq27
    | exact resolve eq27 eq25520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq27440 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq25449
       grind)
    | exact superpose eq25449 eq57
    | exact resolve eq57 eq25449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq27558 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq25363 eq27440
    | exact resolve eq27440 eq25363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27440
  have eq27585 : y = (M.op x y) := by
    first
    | (have i₁ := eq27558
       have i₂ := eq25449
       grind)
    | exact superpose eq25449 eq27558
    | exact resolve eq27558 eq25449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25449 eq27558
  have eq27595 : y = (M.op x y) := by
    first
    | (have i₁ := eq27585
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27585
    | exact resolve eq27585 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27585
  have eq27602 : x = y := by
    first
    | exact superpose eq25363 eq27595
    | exact resolve eq27595 eq25363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25363 eq27595
  have eq27606 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq27602
       grind)
    | exact superpose eq27602 eq25
    | exact resolve eq25 eq27602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq27602
  have eq27760 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27606
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27606
    | exact resolve eq27606 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27606
  have eq27826 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25520 eq27760
    | exact resolve eq27760 eq25520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27760
  have eq28111 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25520 eq15172
    | (have j0 := eq15172 X0
       grind)
    | exact resolve eq15172 eq25520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq28112 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28111 X0
       grind)
    | (have r₁ := eq28111 X0
       have r₂ := eq28
       grind)
    | exact resolve eq28111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28111
  have eq28113 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25520 eq28112
    | (have j0 := eq28112 X0
       grind)
    | exact resolve eq28112 eq25520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28112
  have eq28114 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27826 eq28113
    | (have j0 := eq28113 X0
       grind)
    | exact resolve eq28113 eq27826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28113
  have eq28115 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ (M.op x y))) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27826 eq28114
    | exact resolve eq28114 eq27826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28114
  have eq28116 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq25520 eq28115
    | exact resolve eq28115 eq25520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25520 eq28115
  have eq28250 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28116 eq426
    | exact resolve eq426 eq28116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq28116
  have eq28299 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq28250
  have eq28480 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27826 eq25553
    | exact resolve eq25553 eq27826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25553 eq27826
  have eq28481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28299 eq28480
    | exact resolve eq28480 eq28299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28299 eq28480
  have eq28482 : False := by grind
  exact eq28482

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0
       have i₂ := eq31 X0 X1 X2 X3
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq31
    | exact resolve eq31 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 y y
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq197 X0 X1
       grind)
    | exact superpose eq197 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq197 X1 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq197 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq197 X0 X1
       grind)
    | exact resolve eq12 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq197 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq411 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq394
    | (have j0 := eq394 X0 X1
       grind)
    | exact resolve eq394 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq426 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq411 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq411
    | (have j0 := eq411 (τ X0)
       grind)
    | exact resolve eq411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq411
  have eq428 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq426 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq426
    | (have j0 := eq426 X0
       grind)
    | exact resolve eq426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq431 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq428 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq428
    | (have j0 := eq428 X0
       grind)
    | exact resolve eq428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq627 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1071 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X1) X0) X5)) X6) X1) X6) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq70 X1 (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X0 X5 X6
       have i₂ := eq31 X0 X2 X3 X4
       grind)
    | exact superpose eq31 eq70
    | exact resolve eq70 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq70
  have eq6221 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq203 (M.op (τ X0) (τ X0)) X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq203
    | (have j0 := eq203 (τ X0) X0
       grind)
    | exact resolve eq203 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq6360 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6221 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6221
    | (have j0 := eq6221 X0
       grind)
    | exact resolve eq6221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6221
  have eq6389 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6360 X0
       have i₂ := eq90 (τ X0) (τ X0)
       grind)
    | exact superpose eq90 eq6360
    | (have j0 := eq6360 X0
       grind)
    | exact resolve eq6360 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq6390 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6404 : ∀ X0 : G, (k (k (σ (τ X0)) X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6390 X0
       have i₂ := eq203 (τ X0) X0
       grind)
    | exact superpose eq203 eq6390
    | (have j0 := eq6390 X0
       have j1 := eq203 (τ X0) X0
       grind)
    | exact resolve eq6390 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq6423 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq6390 (σ X0)
       grind)
    | exact superpose eq6390 eq22
    | (have j1 := eq6390 (σ X0)
       grind)
    | exact resolve eq22 eq6390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6390
  have eq6435 : ∀ X0 : G, (k (k (σ (τ X0)) X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6404
  have eq6448 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6423 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq6423
    | (have j0 := eq6423 X0
       grind)
    | exact resolve eq6423 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6457 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6435 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6435
    | (have j0 := eq6435 X0
       grind)
    | exact resolve eq6435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6470 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6448 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6448
    | (have j0 := eq6448 X0
       grind)
    | exact resolve eq6448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq6483 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6470 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6470
    | (have j0 := eq6470 X0
       grind)
    | exact resolve eq6470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6470
  have eq6612 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 (τ X0)
       have i₂ := eq6457 X0
       grind)
    | exact superpose eq6457 eq75
    | (have j1 := eq6457 X0
       grind)
    | (have r₁ := eq75 (τ X0)
       have r₂ := eq6457 X0
       grind)
    | exact resolve eq75 eq6457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq6634 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq6457 X0
       grind)
    | exact superpose eq6457 eq12
    | (have j1 := eq6457 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq6457 X0
       grind)
    | exact resolve eq12 eq6457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6457
  have eq6693 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6634
  have eq6694 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6612
  have eq6718 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6693 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq6693
    | (have j0 := eq6693 X0
       grind)
    | exact resolve eq6693 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693
  have eq6726 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6694 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq6694
    | (have j0 := eq6694 X0
       grind)
    | exact resolve eq6694 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6694
  have eq7131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq391
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq391
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq391 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq7134 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq7131
  have eq10621 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 (τ X0) (τ X0)
       have i₂ := eq6726 X0
       grind)
    | exact superpose eq6726 eq107
    | (have j1 := eq6726 X0
       grind)
    | exact resolve eq107 eq6726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6726
  have eq10664 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10621 X0
       have j1 := eq6718 X0
       grind)
    | (have r₁ := eq10621 X0
       have r₂ := eq6718 X0
       grind)
    | exact resolve eq10621 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718 eq10621
  have eq10673 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10664 X0
       have i₂ := eq33 X0 (k X0 X0)
       grind)
    | exact superpose eq33 eq10664
    | (have j0 := eq10664 X0
       grind)
    | exact resolve eq10664 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq10664
  have eq22184 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (τ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq10673 X0
       grind)
    | exact superpose eq10673 eq11
    | (have j1 := eq10673 X0
       grind)
    | exact resolve eq11 eq10673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10673
  have eq22244 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22184 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq22184
    | (have j0 := eq22184 X0
       grind)
    | exact resolve eq22184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22184
  have eq22289 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22244 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq22244
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq22244 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22244
  have eq22416 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22289 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22289
  have eq22453 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22416 X0
       have j1 := eq107 X0 X0
       grind)
    | (have r₁ := eq22416 x
       have r₂ := eq107 x x
       grind)
    | exact resolve eq22416 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq22416
  have eq22793 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22453
  have eq22801 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22793 X0
       have j1 := eq6483 X0
       grind)
    | (have r₁ := eq22793 X0
       have r₂ := eq6483 X0
       grind)
    | exact resolve eq22793 eq6483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483 eq22793
  have eq22851 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq22801 (σ X0)
       grind)
    | exact superpose eq22801 eq22
    | exact resolve eq22 eq22801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq22897 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22851 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22851
    | exact resolve eq22851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22851
  have eq31070 : y = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq22897 y
       have i₂ := eq7134
       grind)
    | exact superpose eq7134 eq22897
    | exact resolve eq22897 eq7134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7134
  have eq31253 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31070
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq31070
    | exact resolve eq31070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31070
  have eq31266 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq431 y
       grind)
    | (have r₁ := eq31253
       have r₂ := eq431 y
       grind)
    | exact resolve eq31253 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31253
  have eq31310 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90 (σ y) (σ x)
       have i₂ := eq31266
       grind)
    | exact superpose eq31266 eq90
    | exact resolve eq90 eq31266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31266
  have eq31412 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq22897 y
       have i₂ := eq31310
       grind)
    | exact superpose eq31310 eq22897
    | exact resolve eq22897 eq31310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22897 eq31310
  have eq31595 : y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31412
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq31412
    | exact resolve eq31412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31412
  have eq31608 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq431 y
       grind)
    | (have r₁ := eq31595
       have r₂ := eq431 y
       grind)
    | exact resolve eq31595 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq31595
  have eq31614 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq31608
       grind)
    | exact superpose eq31608 eq76
    | exact resolve eq76 eq31608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31709 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq627 y y x
       have i₂ := eq31608
       grind)
    | exact superpose eq31608 eq627
    | exact resolve eq627 eq31608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31608
  have eq31734 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq31709 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq31709
    | exact resolve eq31709 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31709
  have eq34074 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq31614 X0
       have i₂ := eq31734 X0
       grind)
    | exact superpose eq31734 eq31614
    | exact resolve eq31614 eq31734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31614 eq31734
  have eq34225 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq34074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34074
  have eq34269 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 y x
       have i₂ := eq34225 X0
       grind)
    | exact superpose eq34225 eq90
    | (have j1 := eq34225 y
       grind)
    | exact resolve eq90 eq34225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34225
  have eq34329 : y = (M.op y y) := by
    first
    | (have j0 := eq34269 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34269
  have eq34380 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq34329
       grind)
    | exact superpose eq34329 eq76
    | exact resolve eq76 eq34329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq34416 : y = (k y y) := by
    first
    | (have i₁ := eq22801 y
       have i₂ := eq34329
       grind)
    | exact superpose eq34329 eq22801
    | exact resolve eq22801 eq34329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22801
  have eq34481 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq627 y y x
       have i₂ := eq34329
       grind)
    | exact superpose eq34329 eq627
    | exact resolve eq627 eq34329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34507 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq34481 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq34481
    | exact resolve eq34481 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq34481
  have eq35026 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq419 y y
       have i₂ := eq34416
       grind)
    | exact superpose eq34416 eq419
    | (have j0 := eq419 y y
       grind)
    | exact resolve eq419 eq34416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq34416
  have eq35035 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq35026
  have eq35036 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq35035
  have eq36048 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34380 X0
       have i₂ := eq34507 X0
       grind)
    | exact superpose eq34507 eq34380
    | exact resolve eq34380 eq34507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34380
  have eq36050 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq34507 X0
       have i₂ := eq36048 X0
       grind)
    | exact superpose eq36048 eq34507
    | exact resolve eq34507 eq36048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34507
  have eq36165 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq627 y X1 X0
       have i₂ := eq36048 X0
       grind)
    | exact superpose eq36048 eq627
    | exact resolve eq627 eq36048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq36347 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36165 X0 X0
       have i₂ := eq36048 X0
       grind)
    | exact superpose eq36048 eq36165
    | exact resolve eq36165 eq36048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36165
  have eq39986 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op y (M.op (M.op y (M.op y X1)) X2)) X0) y) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1071 y X0 y X1 X2 X3 X4
       have i₂ := eq34329
       grind)
    | exact superpose eq34329 eq1071
    | exact resolve eq1071 eq34329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq34329
  have eq40317 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op y X3)) X4) X0) X4) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq39986 X0 x x X3 X4
       have i₂ := eq36050 (M.op (M.op y (M.op (M.op y (M.op y x)) x)) X0)
       grind)
    | exact superpose eq36050 eq39986
    | exact resolve eq39986 eq36050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39986
  have eq40338 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X3) X4) X0) X4) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq40317 X0 X3 X4
       have i₂ := eq36048 X3
       grind)
    | exact superpose eq36048 eq40317
    | exact resolve eq40317 eq36048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36048 eq40317
  have eq43291 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40338 (σ y) (σ y) X0
       have i₂ := eq35036
       grind)
    | exact superpose eq35036 eq40338
    | exact resolve eq40338 eq35036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35036 eq40338
  have eq43707 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43291 X0
       have i₂ := eq36347 X0 (σ y)
       grind)
    | exact superpose eq36347 eq43291
    | exact resolve eq43291 eq36347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43291
  have eq44288 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36347 X0 (σ y)
       have i₂ := eq43707 X0
       grind)
    | exact superpose eq43707 eq36347
    | exact resolve eq36347 eq43707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36347 eq43707
  have eq45814 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44288 (σ x)
       grind)
    | exact superpose eq44288 eq16
    | exact resolve eq16 eq44288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44288
  have eq45863 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq45814
       have i₂ := eq36050 x
       grind)
    | exact superpose eq36050 eq45814
    | exact resolve eq45814 eq36050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36050 eq45814
  have eq45864 : False := by grind
  exact eq45864

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  clear eq43
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
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
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq124 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq135 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq215 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  clear eq58
  have eq423 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq416 X0
       grind)
    | exact superpose eq416 eq14
    | exact resolve eq14 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq689 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq897 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq423
    | exact resolve eq423 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq423
    | exact resolve eq423 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq915 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq897 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3487 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq691 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq691
    | (have j0 := eq691 (τ X0)
       grind)
    | exact resolve eq691 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3495 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3487 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3487
    | (have j0 := eq3487 X0
       grind)
    | exact resolve eq3487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487
  have eq3501 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3495 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3495
    | (have j0 := eq3495 X0
       grind)
    | exact resolve eq3495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495
  have eq8219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq8220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8219
    | exact resolve eq8219 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8219
  have eq8231 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8220
       have r₂ := eq27
       grind)
    | exact resolve eq8220 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8220
  have eq8233 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8231
    | exact resolve eq8231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8231
  have eq8257 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8233 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq8233
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8233
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8233
       grind)
    | exact resolve eq13 eq8233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8233
  have eq8280 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq8257
  have eq8489 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8280 eq49
    | exact resolve eq49 eq8280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq8280
  have eq8514 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq8489
    | exact resolve eq8489 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8489
  have eq8517 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3501 x
       grind)
    | (have r₁ := eq8514
       have r₂ := eq3501 x
       grind)
    | exact resolve eq8514 eq3501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501 eq8514
  have eq8518 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq8517
       grind)
    | exact superpose eq8517 eq56
    | exact resolve eq56 eq8517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8519 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq8517
       grind)
    | exact superpose eq8517 eq59
    | exact resolve eq59 eq8517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8540 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8517
       grind)
    | exact superpose eq8517 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq8517
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8517
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8517
       grind)
    | exact resolve eq13 eq8517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8517
  have eq8565 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8540
  have eq8587 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq897 eq8519
    | exact resolve eq8519 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8519
  have eq8787 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq691 x
       have i₂ := eq8565
       grind)
    | exact superpose eq8565 eq691
    | (have j0 := eq691 x
       grind)
    | exact resolve eq691 eq8565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq8565
  have eq8790 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8787
  have eq8795 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8790
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8790
    | exact resolve eq8790 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8790
  have eq9037 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8795 eq57
    | exact resolve eq57 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq9038 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8795 eq60
    | exact resolve eq60 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq8795
  have eq9112 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq899 eq9038
    | exact resolve eq9038 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9038
  have eq9378 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8587 eq8518
    | exact resolve eq8518 eq8587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8518 eq8587
  have eq9410 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9378
  have eq9411 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9410
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9410
    | exact resolve eq9410 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9410
  have eq9621 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9411 eq51
    | (have r₁ := eq51
       have r₂ := eq9411
       grind)
    | exact resolve eq51 eq9411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9624 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9411 eq215
    | exact resolve eq215 eq9411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9650 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9411 eq899
    | exact resolve eq899 eq9411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9654 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9621
  have eq10016 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9654 eq96
    | exact resolve eq96 eq9654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654
  have eq10033 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq10016
    | exact resolve eq10016 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10016
  have eq10036 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10033
       have r₂ := eq50
       grind)
    | exact resolve eq10033 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10033
  have eq10045 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10036
       grind)
    | exact superpose eq10036 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq10036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10036
  have eq10046 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10045
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10045
    | exact resolve eq10045 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq10047 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10046
  have eq10057 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10047
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10047
    | exact resolve eq10047 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10047
  have eq10843 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq10057
       grind)
    | exact superpose eq10057 eq56
    | exact resolve eq56 eq10057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10844 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq10057
       grind)
    | exact superpose eq10057 eq59
    | exact resolve eq59 eq10057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq10057
  have eq10927 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq897 eq10844
    | exact resolve eq10844 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10844
  have eq11578 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9112 eq9037
    | exact resolve eq9037 eq9112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9037 eq9112
  have eq11614 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11578
  have eq11616 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11614
    | exact resolve eq11614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11614
  have eq11631 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11616 eq27
    | exact resolve eq27 eq11616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11616
  have eq11816 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9650 eq9624
    | exact resolve eq9624 eq9650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9624 eq9650
  have eq11858 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11816
  have eq11860 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11858
    | exact resolve eq11858 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11858
  have eq11902 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11860 eq9411
    | exact resolve eq9411 eq11860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9411 eq11860
  have eq11907 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11902
  have eq11914 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11907 eq29
    | exact resolve eq29 eq11907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11907
  have eq12073 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq11914
    | exact resolve eq11914 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11914
  have eq12076 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12073 eq20
    | exact resolve eq20 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12073
  have eq12221 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12076
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12076
    | exact resolve eq12076 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq12309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12221 eq11631
    | (have r₁ := eq11631
       have r₂ := eq12221
       grind)
    | exact resolve eq11631 eq12221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12221
  have eq12319 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq12309
  have eq12320 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12319
  have eq12377 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12320 eq51
    | (have r₁ := eq51
       have r₂ := eq12320
       grind)
    | exact resolve eq51 eq12320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq12320
  have eq12420 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12377
  have eq13584 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12420 eq96
    | exact resolve eq96 eq12420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq12420
  have eq13605 : y = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13584
    | exact resolve eq13584 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13584
  have eq13608 : y = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq13605
       have r₂ := eq50
       grind)
    | exact resolve eq13605 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13605
  have eq25659 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10927 eq10843
    | exact resolve eq10843 eq10927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10843 eq10927
  have eq25709 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq25659
  have eq25711 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25709
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25709
    | exact resolve eq25709 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25709
  have eq25712 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq25711
  have eq25833 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25712 eq20
    | exact resolve eq20 eq25712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25918 : x ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25712 eq915
    | (have r₁ := eq915
       have r₂ := eq25712
       grind)
    | exact resolve eq915 eq25712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25712
  have eq25935 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25918
       have r₂ := eq13608
       grind)
    | exact resolve eq25918 eq13608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13608 eq25918
  have eq25988 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25833
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25833
    | exact resolve eq25833 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25833
  have eq25989 : y = (k y x) := by
    first
    | (have r₁ := eq25935
       have r₂ := eq50
       grind)
    | exact resolve eq25935 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq25935
  have eq25992 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq25989
       grind)
    | exact superpose eq25989 eq86
    | exact resolve eq86 eq25989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq25989
  have eq26027 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25992
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25992
    | exact resolve eq25992 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25992
  have eq26286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25988 eq11631
    | (have r₁ := eq11631
       have r₂ := eq25988
       grind)
    | exact resolve eq11631 eq25988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11631
  have eq26310 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25988 eq26027
    | exact resolve eq26027 eq25988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26027
  have eq26326 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26286
  have eq26327 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26326
  have eq26409 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26327 eq215
    | exact resolve eq215 eq26327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq26439 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26327 eq899
    | exact resolve eq899 eq26327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq26327
  have eq26672 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26310 eq135
    | exact resolve eq135 eq26310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq26310
  have eq26696 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq26672
    | exact resolve eq26672 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq26672
  have eq26699 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq26696
       have r₂ := eq915
       grind)
    | exact resolve eq26696 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq26696
  have eq30080 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26439 eq26409
    | exact resolve eq26409 eq26439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26409 eq26439
  have eq30147 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30080
  have eq30151 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30147
    | exact resolve eq30147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30147
  have eq30158 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30151 eq27
    | exact resolve eq27 eq30151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30151
  have eq30246 : x = (M.op x y) := by
    first
    | (have r₁ := eq30158
       have r₂ := eq25988
       grind)
    | exact resolve eq30158 eq25988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25988 eq30158
  have eq30250 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30246 eq20
    | exact resolve eq20 eq30246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30337 : x = (M.op x x) := by
    first
    | exact superpose eq30246 eq897
    | exact resolve eq897 eq30246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq30351 : x = (k x x) := by
    first
    | exact superpose eq30246 eq26699
    | exact resolve eq26699 eq30246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26699
  have eq30423 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30250
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30250
    | exact resolve eq30250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30250
  have eq30457 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30423 eq26
    | exact resolve eq26 eq30423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30674 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq30337
       grind)
    | exact superpose eq30337 eq56
    | exact resolve eq56 eq30337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq30795 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq30246 eq30674
    | exact resolve eq30674 eq30246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30674
  have eq30822 : y = (M.op x y) := by
    first
    | (have i₁ := eq30795
       have i₂ := eq30337
       grind)
    | exact superpose eq30337 eq30795
    | exact resolve eq30795 eq30337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30337 eq30795
  have eq30832 : y = (M.op x y) := by
    first
    | (have i₁ := eq30822
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30822
    | exact resolve eq30822 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq30822
  have eq30839 : x = y := by
    first
    | exact superpose eq30246 eq30832
    | exact resolve eq30832 eq30246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30246 eq30832
  have eq30843 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30839
       grind)
    | exact superpose eq30839 eq24
    | exact resolve eq24 eq30839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30839
  have eq31012 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30843
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30843
    | exact resolve eq30843 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30843
  have eq31081 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30423 eq31012
    | exact resolve eq31012 eq30423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31012
  have eq31437 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq690 x x
       have i₂ := eq30351
       grind)
    | exact superpose eq30351 eq690
    | (have j0 := eq690 x x
       grind)
    | exact resolve eq690 eq30351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq30351
  have eq31438 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31437
  have eq31439 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31438
  have eq31455 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31439
    | exact resolve eq31439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31439
  have eq31474 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30423 eq31455
    | exact resolve eq31455 eq30423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30423 eq31455
  have eq31776 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq31081 eq30457
    | exact resolve eq30457 eq31081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30457 eq31081
  have eq31938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31474 eq31776
    | exact resolve eq31776 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31474 eq31776
  have eq31939 : False := by grind
  exact eq31939

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq179 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq41
    | exact resolve eq41 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq73
  have eq236 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq375 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq14
    | exact resolve eq14 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq369 (σ X0)
       have i₂ := eq90 X0 X0
       grind)
    | exact superpose eq90 eq369
    | (have j1 := eq90 X0 X0
       grind)
    | exact resolve eq369 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq540 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq541 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq543 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq545 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq546 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq543
    | (have j0 := eq543 X0
       grind)
    | exact resolve eq543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq585 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq236 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq236
    | (have j0 := eq236 X0 y
       grind)
    | exact resolve eq236 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq639 : (k (k y y) y) = (τ (k (k (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq84 eq585
    | exact resolve eq585 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq585
  have eq928 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq931 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq375
    | exact resolve eq375 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq375
    | exact resolve eq375 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq1042 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op x X0)
       have i₂ := eq928 x X0
       grind)
    | exact superpose eq928 eq54
    | exact resolve eq54 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1047 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op sF2 x)
       have i₂ := eq928 sF2 x
       grind)
    | exact superpose eq928 eq55
    | exact resolve eq55 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq3591 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq541 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq541
    | (have j0 := eq541 (τ X0)
       grind)
    | exact resolve eq541 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq3599 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3591 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3591
    | (have j0 := eq3591 X0
       grind)
    | exact resolve eq3591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591
  have eq3605 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3599 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3599
    | (have j0 := eq3599 X0
       grind)
    | exact resolve eq3599 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq5734 : (k (k y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq639
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq639
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq5763 : (k (k y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5734
  have eq5764 : (k (k y y) y) = (τ (M.op (M.op (σ y) (σ y)) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5763
  have eq5765 : (τ (σ y)) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5764
       have i₂ := eq369 sF3
       grind)
    | exact superpose eq369 eq5764
    | exact resolve eq5764 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5764
  have eq5766 : y = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq5765
    | exact resolve eq5765 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5765
  have eq6888 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq546 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq546
    | exact resolve eq546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq6995 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6888 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq6888
    | (have j0 := eq6888 X0
       grind)
    | exact resolve eq6888 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6888
  have eq7013 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6995 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6995
    | (have j0 := eq6995 X0
       grind)
    | exact resolve eq6995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6995
  have eq7027 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7013 X0
       have i₂ := eq39 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq39 eq7013
    | (have j0 := eq7013 X0
       grind)
    | exact resolve eq7013 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7013
  have eq7037 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7027 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq7027
    | (have j0 := eq7027 X0
       grind)
    | exact resolve eq7027 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq7027
  have eq7044 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7037 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7037
    | (have j0 := eq7037 X0
       grind)
    | exact resolve eq7037 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7037
  have eq7449 : (σ y) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq5766
       grind)
    | exact superpose eq5766 eq179
    | exact resolve eq179 eq5766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5766
  have eq7452 : (σ y) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7449
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq7449
    | exact resolve eq7449 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449
  have eq23737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23737
    | exact resolve eq23737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23737
  have eq23755 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23744
       have r₂ := eq28
       grind)
    | exact resolve eq23744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23744
  have eq23762 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq23755
  have eq23799 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23762
    | exact resolve eq23762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23762
  have eq24081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23799 eq110
    | exact resolve eq110 eq23799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq23799
  have eq24096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24081
  have eq24099 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24096
       have r₂ := eq28
       grind)
    | exact resolve eq24096 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24096
  have eq24123 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq27292 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24123 eq50
    | exact resolve eq50 eq24123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq24123
  have eq28356 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24099 eq27292
    | exact resolve eq27292 eq24099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24099 eq27292
  have eq28415 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28356
  have eq28423 : x = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq28415
    | exact resolve eq28415 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28415
  have eq28425 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3605 x
       grind)
    | (have r₁ := eq28423
       have r₂ := eq3605 x
       grind)
    | exact resolve eq28423 eq3605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605 eq28423
  have eq28796 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq28425
       grind)
    | exact superpose eq28425 eq106
    | exact resolve eq106 eq28425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq28802 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq369 y
       have i₂ := eq28425
       grind)
    | exact superpose eq28425 eq369
    | exact resolve eq369 eq28425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28841 : x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq928 y y
       have i₂ := eq28425
       grind)
    | exact superpose eq28425 eq928
    | exact resolve eq928 eq28425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq28425
  have eq28850 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28802
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28802
    | exact resolve eq28802 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28802
  have eq28852 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28796
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28796
    | exact resolve eq28796 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28796
  have eq28853 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq28850
       grind)
    | exact superpose eq28850 eq51
    | exact resolve eq51 eq28850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq28870 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1042 x
       have i₂ := eq28850
       grind)
    | exact superpose eq28850 eq1042
    | exact resolve eq1042 eq28850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq28850
  have eq28935 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq931 eq28870
    | exact resolve eq28870 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq28870
  have eq29144 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28935 eq28853
    | exact resolve eq28853 eq28935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28853 eq28935
  have eq29184 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq29144
  have eq29185 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29184
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29184
    | exact resolve eq29184 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29184
  have eq29186 : y = (M.op x y) := by grind
  clear eq29185
  have eq29187 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29186 eq21
    | exact resolve eq21 eq29186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29186
  have eq29356 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29187
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29187
    | exact resolve eq29187 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29187
  have eq29361 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq29356 eq27
    | exact resolve eq27 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq29365 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq29356 eq52
    | exact resolve eq52 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq30950 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7452
       have i₂ := eq7044 sF3
       grind)
    | exact superpose eq7044 eq7452
    | (have j1 := eq7044 (σ y)
       grind)
    | exact resolve eq7452 eq7044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7044 eq7452
  have eq30953 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq30950
  have eq30974 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq29356 eq30953
    | exact resolve eq30953 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30953
  have eq31022 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq29356 eq30974
    | exact resolve eq30974 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30974
  have eq31756 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29356 eq28852
    | exact resolve eq28852 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28852
  have eq31777 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq31756 eq31022
    | exact resolve eq31022 eq31756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31022
  have eq31800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29361 eq31777
    | exact resolve eq31777 eq29361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31777
  have eq31811 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq31800
       have r₂ := eq28
       grind)
    | exact resolve eq31800 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31800
  have eq31824 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq31811
  have eq38690 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq31824 eq31756
    | exact resolve eq31756 eq31824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31756 eq31824
  have eq38710 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38690
  have eq38745 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq38710 eq369
    | exact resolve eq369 eq38710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq38710
  have eq38798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29361 eq38745
    | exact resolve eq38745 eq29361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38745
  have eq38802 : x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq38798
       have r₂ := eq28
       grind)
    | exact resolve eq38798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38798
  have eq38830 : (k x x) = (M.op x x) ∨ x = y := by grind
  have eq39036 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq38830
       grind)
    | exact superpose eq38830 eq44
    | exact resolve eq44 eq38830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq38830
  have eq40210 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq39036
       have i₂ := eq38802
       grind)
    | exact superpose eq38802 eq39036
    | exact resolve eq39036 eq38802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38802 eq39036
  have eq40291 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq40210
  have eq40329 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40291
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40291
    | exact resolve eq40291 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40291
  have eq40372 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq40329 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq40329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40329
  have eq40385 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq40372
  have eq40432 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = y := by
    first
    | exact superpose eq40385 eq1047
    | exact resolve eq1047 eq40385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq40441 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq40385 eq29365
    | exact resolve eq29365 eq40385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29365 eq40385
  have eq40515 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq934 eq40432
    | exact resolve eq40432 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq40432
  have eq40716 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq40515 eq40441
    | exact resolve eq40441 eq40515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40441 eq40515
  have eq40762 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by grind
  clear eq40716
  have eq40763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29361 eq40762
    | exact resolve eq40762 eq29361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40762
  have eq40764 : x = y := by
    first
    | (have r₁ := eq40763
       have r₂ := eq28
       grind)
    | exact resolve eq40763 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40763
  have eq40766 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40764
       grind)
    | exact superpose eq40764 eq25
    | exact resolve eq25 eq40764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq40875 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28841
       have i₂ := eq40764
       grind)
    | exact superpose eq40764 eq28841
    | exact resolve eq28841 eq40764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28841 eq40764
  have eq40904 : x = (M.op x x) := by grind
  clear eq40875
  have eq41021 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq29356 eq40766
    | exact resolve eq40766 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29356 eq40766
  have eq41122 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41021
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq41021
    | exact resolve eq41021 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41021
  have eq41272 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41122 eq29361
    | exact resolve eq29361 eq41122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29361
  have eq41485 : (k x x) = (M.op x x) := by grind
  have eq41555 : x = (k x x) := by
    first
    | (have i₁ := eq41485
       have i₂ := eq40904
       grind)
    | exact superpose eq40904 eq41485
    | exact resolve eq41485 eq40904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40904 eq41485
  have eq42453 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq545 x
       have i₂ := eq41555
       grind)
    | exact superpose eq41555 eq545
    | (have j0 := eq545 x
       grind)
    | exact resolve eq545 eq41555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq41555
  have eq42476 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq42453
  have eq42489 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42476
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42476
    | exact resolve eq42476 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq42476
  have eq42508 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41122 eq42489
    | exact resolve eq42489 eq41122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41122 eq42489
  have eq42527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41272 eq42508
    | exact resolve eq42508 eq41272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41272 eq42508
  have eq42545 : False := by grind
  exact eq42545

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq70
    | exact resolve eq70 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq74
    | exact resolve eq74 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq85 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq517 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq525 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq14
    | exact resolve eq14 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq525
    | exact resolve eq525 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq24693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq24693
    | exact resolve eq24693 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24693
  have eq24711 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24700
       have r₂ := eq29
       grind)
    | exact resolve eq24700 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24700
  have eq24735 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24711 eq88
    | exact resolve eq88 eq24711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24770 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24711 eq953
    | exact resolve eq953 eq24711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24711
  have eq24776 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq24770
    | exact resolve eq24770 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24770
  have eq24782 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24776 eq517
    | exact resolve eq517 eq24776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24776
  have eq24822 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq24782
    | exact resolve eq24782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24782
  have eq24823 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq24822
  have eq24847 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88 x
       have i₂ := eq24823
       grind)
    | exact superpose eq24823 eq88
    | exact resolve eq88 eq24823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq24823
  have eq26032 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq24847
       grind)
    | exact superpose eq24847 eq46
    | exact resolve eq46 eq24847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24847
  have eq26064 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26032
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq26032
    | exact resolve eq26032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26032
  have eq26392 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26064 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26064
  have eq26401 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq26392
    | exact resolve eq26392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26392
  have eq26402 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq26401
  have eq31360 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26402 eq953
    | exact resolve eq953 eq26402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26402
  have eq31367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq31360
    | exact resolve eq31360 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31360
  have eq31368 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq31367
  have eq31779 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31368 eq517
    | exact resolve eq517 eq31368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31368
  have eq31826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq31779
    | exact resolve eq31779 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31779
  have eq31827 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31826
  have eq31838 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31827
  have eq31897 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq31838
       grind)
    | exact superpose eq31838 eq46
    | exact resolve eq46 eq31838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq31838
  have eq31929 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31897
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq31897
    | exact resolve eq31897 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31897
  have eq32081 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31929 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq31929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31929
  have eq32089 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq32081
    | exact resolve eq32081 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32081
  have eq32090 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq32089
  have eq33900 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32090 eq953
    | exact resolve eq953 eq32090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32090
  have eq33909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq33900
    | exact resolve eq33900 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33900
  have eq33910 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33909
  have eq33921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33910 eq517
    | exact resolve eq517 eq33910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33910
  have eq33968 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq33921
    | exact resolve eq33921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33921
  have eq33969 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33968
  have eq33971 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq33969 eq29
    | exact resolve eq29 eq33969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33969
  have eq64360 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24735 eq75
    | exact resolve eq75 eq24735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24735
  have eq64378 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq64360
  have eq64387 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq64378
       have r₂ := eq33971
       grind)
    | exact resolve eq64378 eq33971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64378
  have eq64400 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq64387
  have eq64758 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq64400 eq75
    | exact resolve eq75 eq64400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq64400
  have eq64775 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq64758
  have eq64783 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq64775
       have r₂ := eq33971
       grind)
    | exact resolve eq64775 eq33971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64775
  have eq64857 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq953 x x
       have i₂ := eq64783
       grind)
    | exact superpose eq64783 eq953
    | exact resolve eq953 eq64783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq64783
  have eq64877 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64857
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq64857
    | exact resolve eq64857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64857
  have eq64892 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq517 y
       have i₂ := eq64877
       grind)
    | exact superpose eq64877 eq517
    | exact resolve eq517 eq64877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq64877
  have eq64943 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64892
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq64892
    | exact resolve eq64892 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq64892
  have eq64944 : y = (M.op x y) := by grind
  clear eq64943
  have eq65238 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq64944 eq22
    | exact resolve eq22 eq64944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq64944
  have eq65525 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq65238
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq65238
    | exact resolve eq65238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq65238
  have eq65526 : False := by grind
  exact eq65526

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X0 X0) X0 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq62
    | exact resolve eq62 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq80 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq75 (τ X0)
       grind)
    | exact superpose eq75 eq19
    | exact resolve eq19 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq83 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq23
    | exact resolve eq23 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq85 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq117 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq84 (σ X0)
       grind)
    | exact superpose eq84 eq23
    | exact resolve eq23 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq118 : ∀ X0 : G, (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq80
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0) X5) X4) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 X4 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X0 X5
       have i₂ := eq63 X2 X1 X3 X0
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq571 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq14 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact superpose eq14 eq85
    | (have j1 := eq14 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq587 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq679 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq554 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq554
    | (have j0 := eq554 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq554 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq554 (M.op X0 X0) X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq554
    | (have j0 := eq554 (M.op X0 X0) X0
       grind)
    | exact resolve eq554 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq807 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq2828 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq807 X0
       grind)
    | exact superpose eq807 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq807 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq807 X0
       grind)
    | exact resolve eq13 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2860 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2861 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2860 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2876 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2861 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq2861
    | (have j0 := eq2861 X0
       grind)
    | exact resolve eq2861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861
  have eq2880 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2876 X0
       have i₂ := eq75 X0
       grind)
    | (have i₁ := eq2876 X0
       have i₂ := eq75 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq75 eq2876
    | (have j0 := eq2876 X0
       grind)
    | exact resolve eq2876 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2876
  have eq2882 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2880 eq807
    | (have j0 := eq807 X0
       have j1 := eq2880 X0
       grind)
    | exact resolve eq807 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq2883 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2880 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2880
    | exact resolve eq2880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880
  have eq3384 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2882 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3669 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2883 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2883
  have eq4026 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq576 (τ X0) X0
       grind)
    | exact superpose eq576 eq85
    | (have j1 := eq576 (τ X0) X0
       grind)
    | exact resolve eq85 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq576
  have eq4049 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq4026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq4058 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4049 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4049
    | (have j0 := eq4049 X0
       grind)
    | exact resolve eq4049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049
  have eq4145 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3384 (τ X0)
       have i₂ := eq4058 X0
       grind)
    | exact superpose eq4058 eq3384
    | (have j0 := eq3384 (τ X0)
       have j1 := eq4058 X0
       grind)
    | exact resolve eq3384 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384 eq4058
  have eq4185 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4145
  have eq4199 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4185 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4185
    | (have j0 := eq4185 X0
       grind)
    | exact resolve eq4185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq4240 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq4199 X0
       grind)
    | exact superpose eq4199 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq4199 X0
       grind)
    | exact resolve eq14 eq4199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq4249 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240
  have eq8495 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq126 X0 (k X0 X0)
       have i₂ := eq4249 X0
       grind)
    | exact superpose eq4249 eq126
    | (have j1 := eq4249 X0
       grind)
    | exact resolve eq126 eq4249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4249
  have eq8603 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8495
  have eq8740 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8603 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq8603
    | (have j0 := eq8603 (τ X0)
       grind)
    | exact resolve eq8603 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8763 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq8603 (σ X0)
       grind)
    | exact superpose eq8603 eq29
    | (have j1 := eq8603 (σ X0)
       grind)
    | exact resolve eq29 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8603
  have eq8781 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8763 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8763
    | (have j0 := eq8763 X0
       grind)
    | exact resolve eq8763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8763
  have eq8792 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2882 eq8781
    | (have j0 := eq8781 X0
       have j1 := eq2882 X0
       grind)
    | exact resolve eq8781 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882 eq8781
  have eq8794 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8792 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq8792
    | (have j0 := eq8792 X0
       grind)
    | exact resolve eq8792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8792
  have eq9594 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq8794 X0
       grind)
    | exact superpose eq8794 eq84
    | (have j1 := eq8794 X0
       grind)
    | exact resolve eq84 eq8794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9595 : ∀ X0 : G, (k (τ (τ (σ (σ X0)))) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq8794 (σ X0)
       grind)
    | exact superpose eq8794 eq118
    | (have j1 := eq8794 (σ X0)
       grind)
    | exact resolve eq118 eq8794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq9601 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) X1
       have i₂ := eq8794 X0
       grind)
    | exact superpose eq8794 eq80
    | (have j1 := eq8794 X0
       grind)
    | exact resolve eq80 eq8794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq9664 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq679 (σ X0) (σ X0) x
       have i₂ := eq8794 X0
       grind)
    | exact superpose eq8794 eq679
    | (have j1 := eq8794 X0
       grind)
    | exact resolve eq679 eq8794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8794
  have eq9681 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9664 X0 X1
       have i₂ := eq126 (σ X0) X1
       grind)
    | exact superpose eq126 eq9664
    | (have j0 := eq9664 X0 X1
       grind)
    | exact resolve eq9664 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9664
  have eq9710 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9595 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq9595
    | (have j0 := eq9595 X0
       grind)
    | exact resolve eq9595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9595
  have eq9711 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9594 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9594
    | (have j0 := eq9594 X0
       grind)
    | exact resolve eq9594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9594
  have eq9717 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9710 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9710
    | (have j0 := eq9710 X0
       grind)
    | exact resolve eq9710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9710
  have eq9722 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9717 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9717
    | (have j0 := eq9717 X0
       grind)
    | exact resolve eq9717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9717
  have eq10040 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq9711 eq9722
    | (have j0 := eq9722 X0
       have j1 := eq9711 X0
       grind)
    | exact resolve eq9722 eq9711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711 eq9722
  have eq10652 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9681 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9681
    | (have j0 := eq9681 (τ X0) X1
       grind)
    | exact resolve eq9681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10765 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10652 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq10652
    | (have j0 := eq10652 X0 X1
       grind)
    | exact resolve eq10652 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10652
  have eq12383 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq8740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12468 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12383 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq12383
    | (have j0 := eq12383 (σ X0)
       grind)
    | exact resolve eq12383 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12383
  have eq12471 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12468 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12468
    | (have j0 := eq12468 X0
       grind)
    | exact resolve eq12468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq12474 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12471 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12471
    | (have j0 := eq12471 X0
       grind)
    | exact resolve eq12471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12471
  have eq13273 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq9681 eq9601
    | (have j0 := eq9601 X0 X1
       have j1 := eq9681 X0 X1
       grind)
    | exact resolve eq9601 eq9681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9601
  have eq13274 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | exact superpose eq13273 eq9681
    | (have j0 := eq9681 X0 X1
       have j1 := eq13273 X0 X1
       grind)
    | exact resolve eq9681 eq13273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9681
  have eq13311 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (σ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq13273 (τ X0) X1
       grind)
    | exact superpose eq13273 eq32
    | (have j1 := eq13273 (τ X0) X1
       grind)
    | exact resolve eq32 eq13273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13327 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13311 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13311
    | (have j0 := eq13311 X0 X1
       grind)
    | exact resolve eq13311 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13311
  have eq13355 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13274 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13274
    | (have j0 := eq13274 (τ X0) X1
       grind)
    | exact resolve eq13274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13542 : ∀ X0 X4 X5 : G, (M.op (M.op (M.op (σ X0) X5) X4) X5) = X5 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq281 (σ X0) x x x X4 X5
       have i₂ := eq13274 X0 (M.op (M.op (M.op (M.op (M.op x x) (M.op x x)) (σ X0)) x) X4)
       grind)
    | exact superpose eq13274 eq281
    | (have j1 := eq13274 X0 x
       grind)
    | exact resolve eq281 eq13274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq13640 : ∀ X0 X4 X5 : G, (M.op (M.op X5 X4) X5) = X5 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4 X5
    first
    | exact superpose eq13273 eq13542
    | (have j0 := eq13542 X0 X4 X5
       have j1 := eq13273 X0 x
       grind)
    | exact resolve eq13542 eq13273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13273 eq13542
  have eq13753 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13355 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq13355
    | (have j0 := eq13355 X0 X1
       grind)
    | exact resolve eq13355 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13355
  have eq13836 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq13640 eq10765
    | (have j0 := eq10765 X0 X1
       have j1 := eq13640 X0 X1 X0
       grind)
    | exact resolve eq10765 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10765
  have eq15035 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12474 X0
       have j1 := eq10040 X0
       grind)
    | (have r₁ := eq12474 X0
       have r₂ := eq10040 X0
       grind)
    | exact resolve eq12474 eq10040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10040 eq12474
  have eq15054 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15035 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15035
    | (have j0 := eq15035 (τ X0)
       grind)
    | exact resolve eq15035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15035
  have eq15209 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq8740 eq15054
    | (have j0 := eq15054 X0
       have j1 := eq8740 X0
       grind)
    | exact resolve eq15054 eq8740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15054
  have eq15222 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq15209 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq15209
    | (have j0 := eq15209 X0
       grind)
    | exact resolve eq15209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209
  have eq15228 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq15222 eq8740
    | (have j0 := eq8740 X0
       have j1 := eq15222 X0
       grind)
    | exact resolve eq8740 eq15222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8740
  have eq15282 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq15222 X0
       grind)
    | exact superpose eq15222 eq9
    | (have j1 := eq15222 X0
       grind)
    | exact resolve eq9 eq15222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15222
  have eq15361 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq13640 eq15282
    | (have j0 := eq15282 X0 X1
       have j1 := eq13640 X0 x x
       grind)
    | exact resolve eq15282 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13640 eq15282
  have eq18192 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3669 (τ X0)
       have i₂ := eq15228 X0
       grind)
    | exact superpose eq15228 eq3669
    | (have j0 := eq3669 (τ X0)
       have j1 := eq15228 X0
       grind)
    | (have r₁ := eq3669 (τ X0)
       have r₂ := eq15228 X0
       grind)
    | exact resolve eq3669 eq15228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15228
  have eq18278 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have j0 := eq18192 X0
       have j1 := eq3669 (τ X0)
       grind)
    | (have r₁ := eq18192 X0
       have r₂ := eq3669 (τ X0)
       grind)
    | exact resolve eq18192 eq3669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3669 eq18192
  have eq22880 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq772 x y
       grind)
    | exact superpose eq772 eq16
    | (have j1 := eq772 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq772 x y
       grind)
    | exact resolve eq16 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23045 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq22880
  have eq71332 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (M.op (M.op X0 X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq587 X0
       grind)
    | exact superpose eq587 eq9
    | (have j1 := eq587 X0
       grind)
    | exact resolve eq9 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq72304 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op (M.op (M.op X0 X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq71332 X0 X1
       grind)
    | exact superpose eq71332 eq10
    | (have j1 := eq71332 X0 X1
       grind)
    | exact resolve eq10 eq71332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71332
  have eq72441 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq13836 eq72304
    | (have j0 := eq72304 X0 X1
       have j1 := eq13836 X0 X1
       grind)
    | exact resolve eq72304 eq13836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72304
  have eq72500 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq72441 eq13836
    | (have j0 := eq13836 X0 X1
       have j1 := eq72441 X0 X1
       grind)
    | exact resolve eq13836 eq72441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13836
  have eq72501 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq72441 eq13327
    | (have j0 := eq13327 X0 X1
       have j1 := eq72441 X0 X1
       grind)
    | exact resolve eq13327 eq72441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13327
  have eq72506 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72441 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72441
    | (have j0 := eq72441 (σ X0) X1
       grind)
    | exact resolve eq72441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72441
  have eq72879 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (k X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq72501 X0 X1
       grind)
    | exact superpose eq72501 eq11
    | (have j1 := eq72501 X0 X1
       grind)
    | exact resolve eq11 eq72501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72501
  have eq73001 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72879 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq72879
    | (have j0 := eq72879 X0 X1
       grind)
    | exact resolve eq72879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72879
  have eq73169 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq73001 (τ X0) X1
       grind)
    | exact superpose eq73001 eq32
    | (have j1 := eq73001 (τ X0) X1
       grind)
    | exact resolve eq32 eq73001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq73001
  have eq73195 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq15361 eq73169
    | (have j0 := eq73169 X0 X1
       have j1 := eq15361 X0 X1
       grind)
    | exact resolve eq73169 eq15361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15361 eq73169
  have eq73460 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq72500 eq13753
    | (have j0 := eq13753 X0 X1
       have j1 := eq72500 X0 X1
       grind)
    | exact resolve eq13753 eq72500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13753 eq72500
  have eq73828 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (k X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq73460 X0 X1
       grind)
    | exact superpose eq73460 eq11
    | (have j1 := eq73460 X0 X1
       grind)
    | exact resolve eq11 eq73460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73460
  have eq73936 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq73828 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq73828
    | (have j0 := eq73828 X0 X1
       grind)
    | exact resolve eq73828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73828
  have eq74088 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73936 (σ X0) X1
       grind)
    | exact superpose eq73936 eq15
    | (have j1 := eq73936 (σ X0) X1
       grind)
    | exact resolve eq15 eq73936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73936
  have eq74136 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq13274 eq74088
    | (have j0 := eq74088 X0 X1
       have j1 := eq13274 X0 X1
       grind)
    | exact resolve eq74088 eq13274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13274 eq74088
  have eq76550 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq72506 X0 X1
       grind)
    | exact superpose eq72506 eq11
    | (have j1 := eq72506 X0 X1
       grind)
    | exact resolve eq11 eq72506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72506
  have eq76858 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126 (σ X0) (σ X0)
       have i₂ := eq76550 X0 X1
       grind)
    | exact superpose eq76550 eq126
    | (have j1 := eq76550 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq126 eq76550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76550
  have eq77226 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126 (τ X0) (τ X0)
       have i₂ := eq73195 X0 X1
       grind)
    | exact superpose eq73195 eq126
    | (have j1 := eq73195 X0 (τ (M.op X0 X0))
       grind)
    | exact resolve eq126 eq73195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73195
  have eq78896 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0)
       have i₂ := eq74136 X0 X1
       grind)
    | exact superpose eq74136 eq71
    | (have j1 := eq74136 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq71 eq74136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq74136
  have eq79340 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78896 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78896
  have eq79341 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79340
  have eq85460 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq76858 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76858
  have eq85461 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq85460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85460
  have eq85637 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq85461 X0
       grind)
    | exact superpose eq85461 eq9
    | exact resolve eq9 eq85461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93564 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq77226 X0 (τ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77226
  have eq93565 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq93564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93564
  have eq93755 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq93565 X0
       grind)
    | exact superpose eq93565 eq9
    | exact resolve eq9 eq93565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93565
  have eq93995 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (τ X0) (τ (M.op X0 X0)) X1
       have i₂ := eq93755 X0 (τ X0)
       grind)
    | exact superpose eq93755 eq77
    | exact resolve eq77 eq93755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq112974 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq93995 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93995
  have eq258948 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq23045
       grind)
    | exact superpose eq23045 eq84
    | exact resolve eq84 eq23045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq259485 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq258948
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq258948
    | exact resolve eq258948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258948
  have eq259585 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq259485
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq259485 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259485
  have eq259586 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq259585
  have eq259696 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq126 (σ x) (σ y)
       have i₂ := eq259586
       grind)
    | exact superpose eq259586 eq126
    | exact resolve eq126 eq259586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259586
  have eq259929 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq259696
       grind)
    | exact superpose eq259696 eq84
    | exact resolve eq84 eq259696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq260038 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (σ (M.op (τ (τ (σ x))) (τ (τ (σ x))))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18278 (σ x)
       have i₂ := eq259696
       grind)
    | exact superpose eq259696 eq18278
    | (have j0 := eq18278 (σ x)
       grind)
    | exact resolve eq18278 eq259696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18278
  have eq260123 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op (τ (σ x)) (M.op (τ (σ x)) X0)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq112974 (σ x) x
       have i₂ := eq259696
       grind)
    | exact superpose eq259696 eq112974
    | exact resolve eq112974 eq259696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112974 eq259696
  have eq260279 : (τ (σ x)) = (σ (M.op (τ (τ (σ x))) (τ (τ (σ x))))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq260038
  have eq260381 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq260123 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq260123
    | exact resolve eq260123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260123
  have eq260442 : x = (σ (M.op (τ x) (τ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq260279
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq260279
    | exact resolve eq260279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260279
  have eq260509 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq259929
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq259929
    | exact resolve eq259929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259929
  have eq260545 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq260381 X0
       have i₂ := eq126 x X0
       grind)
    | exact superpose eq126 eq260381
    | exact resolve eq260381 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260381
  have eq260611 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq260545 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260545
  have eq260739 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq85461 x
       have i₂ := eq260509
       grind)
    | exact superpose eq260509 eq85461
    | exact resolve eq85461 eq260509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260509
  have eq270044 : ∀ X0 : G, (M.op (M.op (M.op (σ (τ x)) X0) x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq85637 (τ x) X0
       have i₂ := eq260442
       grind)
    | exact superpose eq260442 eq85637
    | exact resolve eq85637 eq260442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260442
  have eq270374 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq270044 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq270044
    | exact resolve eq270044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270044
  have eq270482 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq260611 eq270374
    | exact resolve eq270374 eq260611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260611 eq270374
  have eq270779 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq126 x x
       have i₂ := eq270482 X0
       grind)
    | exact superpose eq270482 eq126
    | (have j1 := eq270482 y
       grind)
    | exact resolve eq126 eq270482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270482
  have eq271810 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq270779 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270779
  have eq271811 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq271810
  have eq276670 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq260739
       grind)
    | exact superpose eq260739 eq16
    | exact resolve eq16 eq260739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260739
  have eq276887 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq271811 eq276670
    | exact resolve eq276670 eq271811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271811 eq276670
  have eq276888 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq276887
  have eq277165 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq276888
       grind)
    | exact superpose eq276888 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq276888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276888
  have eq277166 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq277165
  have eq277285 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126 x y
       have i₂ := eq277166
       grind)
    | exact superpose eq277166 eq126
    | exact resolve eq126 eq277166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277166
  have eq277379 : x = (M.op x x) := by grind
  clear eq277285
  have eq277687 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79341 x
       have i₂ := eq277379
       grind)
    | exact superpose eq277379 eq79341
    | exact resolve eq79341 eq277379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79341
  have eq277826 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq679 x x x
       have i₂ := eq277379
       grind)
    | exact superpose eq277379 eq679
    | exact resolve eq679 eq277379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq277379
  have eq277943 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq277826 X0
       have i₂ := eq126 x X0
       grind)
    | exact superpose eq126 eq277826
    | exact resolve eq277826 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq277826
  have eq283925 : ∀ X0 : G, (M.op (M.op (M.op (τ (σ x)) X0) (τ (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq93755 (σ x) X0
       have i₂ := eq277687
       grind)
    | exact superpose eq277687 eq93755
    | exact resolve eq93755 eq277687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93755
  have eq284233 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq283925 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq283925
    | exact resolve eq283925 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283925
  have eq284391 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq284233 X0
       have i₂ := eq277943 X0
       grind)
    | exact superpose eq277943 eq284233
    | exact resolve eq284233 eq277943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284233
  have eq284453 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq277943 X0
       have i₂ := eq284391 X0
       grind)
    | exact superpose eq284391 eq277943
    | exact resolve eq277943 eq284391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277943
  have eq284456 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq284391 y
       grind)
    | exact superpose eq284391 eq16
    | exact resolve eq16 eq284391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287315 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq284456
       have i₂ := eq772 x y
       grind)
    | exact superpose eq772 eq284456
    | (have j1 := eq772 x y
       grind)
    | exact resolve eq284456 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq287318 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq287315
       have i₂ := eq284391 y
       grind)
    | exact superpose eq284391 eq287315
    | exact resolve eq287315 eq284391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287315
  have eq287319 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq287318
  have eq287320 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq287319
       have i₂ := eq277687
       grind)
    | exact superpose eq277687 eq287319
    | exact resolve eq287319 eq277687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287319
  have eq287321 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq287320
       have i₂ := eq284391 y
       grind)
    | exact superpose eq284391 eq287320
    | exact resolve eq287320 eq284391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284391 eq287320
  have eq287322 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq287321
       have i₂ := eq284453 x
       grind)
    | exact superpose eq284453 eq287321
    | exact resolve eq287321 eq284453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287321
  have eq287323 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq287322
  have eq287921 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq85637 x (σ y)
       have i₂ := eq287323
       grind)
    | exact superpose eq287323 eq85637
    | exact resolve eq85637 eq287323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85637 eq287323
  have eq288078 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq287921
       have i₂ := eq85461 x
       grind)
    | exact superpose eq85461 eq287921
    | exact resolve eq287921 eq85461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85461 eq287921
  have eq288120 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq288078
       have i₂ := eq284453 x
       grind)
    | exact superpose eq284453 eq288078
    | exact resolve eq288078 eq284453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284453 eq288078
  have eq288151 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq288120
       have r₂ := eq284456
       grind)
    | exact resolve eq288120 eq284456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288120
  have eq288177 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq288151
       grind)
    | exact superpose eq288151 eq10
    | exact resolve eq10 eq288151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288151
  have eq288500 : x = y ∨ x = y := by
    first
    | (have i₁ := eq288177
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq288177
    | exact resolve eq288177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288177
  have eq288501 : x = y := by grind
  clear eq288500
  have eq288603 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq284456
       have i₂ := eq288501
       grind)
    | exact superpose eq288501 eq284456
    | exact resolve eq284456 eq288501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284456 eq288501
  have eq288604 : False := by grind
  exact eq288604

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq83 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq144 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq127
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq151 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq144
  have eq369 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq375 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq14
    | exact resolve eq14 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq56 X3 X2 X4 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq536 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq369 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq369
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq369 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq541 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq545 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq927 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq375
    | exact resolve eq375 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3590 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq541 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq541
    | (have j0 := eq541 (τ X0)
       grind)
    | exact resolve eq541 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3598 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3590 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3590
    | (have j0 := eq3590 X0
       grind)
    | exact resolve eq3590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590
  have eq3604 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3598 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3598
    | (have j0 := eq3598 X0
       grind)
    | exact resolve eq3598 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3598
  have eq8201 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq442 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq442
    | exact resolve eq442 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq8232 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq8201 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq8201
    | exact resolve eq8201 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8201
  have eq11250 : (M.op (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq151 eq16
    | exact resolve eq16 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq11296 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq150 eq11250
    | exact resolve eq11250 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11250
  have eq23668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23668
    | exact resolve eq23668 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23668
  have eq23686 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23675
       have r₂ := eq28
       grind)
    | exact resolve eq23675 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23675
  have eq23691 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq23686 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq23686
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq23686
       grind)
    | exact resolve eq12 eq23686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23728 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq23686
  have eq23729 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq23691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23691
  have eq23957 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23729 eq91
    | (have j1 := eq23729 (σ (M.op x y))
       grind)
    | exact resolve eq91 eq23729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23729
  have eq23990 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq23957
  have eq24008 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq23990
       have r₂ := eq23728
       grind)
    | exact resolve eq23990 eq23728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23728 eq23990
  have eq24056 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24008
  have eq24094 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq24056
    | exact resolve eq24056 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24056
  have eq24323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24094 eq91
    | exact resolve eq91 eq24094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq24094
  have eq24339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24323
  have eq24342 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq24339
       have r₂ := eq28
       grind)
    | exact resolve eq24339 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24339
  have eq24345 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq375 y X0
       have i₂ := eq24342
       grind)
    | exact superpose eq24342 eq375
    | exact resolve eq375 eq24342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24349 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq24342
       grind)
    | exact superpose eq24342 eq14
    | exact resolve eq14 eq24342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24342
  have eq24400 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24349 X0
       have i₂ := eq927 y X0
       grind)
    | exact superpose eq927 eq24349
    | exact resolve eq24349 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24349
  have eq26671 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24345 X0
       have i₂ := eq24400 X0
       grind)
    | exact superpose eq24400 eq24345
    | exact resolve eq24345 eq24400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24345
  have eq26742 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq26671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26671
  have eq26837 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq927 y y
       have i₂ := eq26742 X0
       grind)
    | exact superpose eq26742 eq927
    | (have j1 := eq26742 x
       grind)
    | exact resolve eq927 eq26742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26742
  have eq27375 : x ≠ x ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j0 := eq26837 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26837
  have eq27376 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27375
  have eq27673 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24400 x
       have i₂ := eq27376
       grind)
    | exact superpose eq27376 eq24400
    | exact resolve eq24400 eq27376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24400 eq27376
  have eq27709 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27673
  have eq27711 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27709
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27709
    | exact resolve eq27709 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27709
  have eq27720 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq369 y
       have i₂ := eq27711
       grind)
    | exact superpose eq27711 eq369
    | exact resolve eq369 eq27711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27711
  have eq27767 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27720
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27720
    | exact resolve eq27720 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27720
  have eq27768 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq27767
  have eq27772 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27768 eq30
    | exact resolve eq30 eq27768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq27768
  have eq27924 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq27772
    | exact resolve eq27772 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27772
  have eq27925 : y = (M.op x y) := by grind
  clear eq27924
  have eq27926 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27925 eq21
    | exact resolve eq21 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28088 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27926
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27926
    | exact resolve eq27926 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27926
  have eq28089 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq28088 eq27
    | exact resolve eq27 eq28088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32978 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq930 eq83
    | exact resolve eq83 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq930
  have eq32979 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq32978
    | exact resolve eq32978 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32978
  have eq32980 : y = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27925 eq32979
    | exact resolve eq32979 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32979
  have eq32981 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27925 eq32980
    | exact resolve eq32980 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32980
  have eq32992 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32981 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq32981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32981
  have eq32999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28089 eq32992
    | exact resolve eq32992 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32992
  have eq33010 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq32999
       have r₂ := eq28
       grind)
    | exact resolve eq32999 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32999
  have eq33562 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11296 eq545
    | (have j0 := eq545 (M.op x y)
       grind)
    | exact resolve eq545 eq11296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq11296
  have eq33809 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq33562
    | exact resolve eq33562 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33562
  have eq33874 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27925 eq33809
    | exact resolve eq33809 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33809
  have eq33911 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq33874
    | exact resolve eq33874 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33874
  have eq33917 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27925 eq33911
    | exact resolve eq33911 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33911
  have eq188496 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33010 eq369
    | exact resolve eq369 eq33010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq33010
  have eq188563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28089 eq188496
    | exact resolve eq188496 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188496
  have eq188583 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq188563
       have r₂ := eq28
       grind)
    | exact resolve eq188563 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188563
  have eq188589 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq188677 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq188589 eq150
    | exact resolve eq150 eq188589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188589
  have eq188824 : (k y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27925 eq188677
    | exact resolve eq188677 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188677
  have eq189632 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq188583 eq188824
    | exact resolve eq188824 eq188583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188583 eq188824
  have eq189790 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq189632
  have eq189826 : (M.op x y) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq189790
    | exact resolve eq189790 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189790
  have eq189840 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27925 eq189826
    | exact resolve eq189826 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189826
  have eq189845 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq3604 y
       grind)
    | (have r₁ := eq189840
       have r₂ := eq3604 y
       grind)
    | exact resolve eq189840 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604 eq189840
  have eq189983 : (k y y) = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq189987 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq375 y X0
       have i₂ := eq189845
       grind)
    | exact superpose eq189845 eq375
    | exact resolve eq375 eq189845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190042 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq8232 y y x
       have i₂ := eq189845
       grind)
    | exact superpose eq189845 eq8232
    | exact resolve eq8232 eq189845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190044 : x ≠ y ∨ x = (M.op y y) := by grind
  have eq190046 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq190042 X0
       have i₂ := eq927 y X0
       grind)
    | exact superpose eq927 eq190042
    | exact resolve eq190042 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190042
  have eq190083 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq189983
       grind)
    | exact superpose eq189983 eq73
    | exact resolve eq73 eq189983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq189983
  have eq190220 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28088 eq190083
    | exact resolve eq190083 eq28088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190083
  have eq191469 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq190220
       have i₂ := eq189845
       grind)
    | exact superpose eq189845 eq190220
    | exact resolve eq190220 eq189845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189845 eq190220
  have eq191670 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq191469
       have r₂ := eq190044
       grind)
    | exact resolve eq191469 eq190044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190044 eq191469
  have eq191683 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq191670
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq191670
    | exact resolve eq191670 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191670
  have eq191688 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28088 eq191683
    | exact resolve eq191683 eq28088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191683
  have eq191820 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq191688 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq191688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191688
  have eq191835 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq191820
  have eq191910 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq191835 eq375
    | exact resolve eq375 eq191835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq191965 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq191835 eq8232
    | exact resolve eq8232 eq191835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191835
  have eq191971 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq191965 x
       have i₂ := eq927 sF1 x
       grind)
    | exact superpose eq927 eq191965
    | exact resolve eq191965 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191965
  have eq193582 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq189987 X0
       have i₂ := eq190046 X0
       grind)
    | exact superpose eq190046 eq189987
    | exact resolve eq189987 eq190046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189987 eq190046
  have eq193726 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq193582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193582
  have eq193960 : x ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq193726 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193726
  have eq200567 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq191971 eq191910
    | exact resolve eq191910 eq191971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191910 eq191971
  have eq200716 : ∀ X0 : G, x = (M.op y y) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq200567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200567
  have eq200766 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33917
       have i₂ := eq200716 X0
       grind)
    | exact superpose eq200716 eq33917
    | (have j1 := eq200716 (σ (M.op x y))
       grind)
    | exact resolve eq33917 eq200716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33917
  have eq200926 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq200766 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq200766
    | (have j0 := eq200766 (σ (M.op x y))
       grind)
    | exact resolve eq200766 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200766
  have eq200948 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28089 eq200926
    | (have j0 := eq200926 (σ (M.op x y))
       grind)
    | exact resolve eq200926 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200926
  have eq200952 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq200948 (σ (M.op x y))
       grind)
    | (have r₁ := eq200948 X0
       have r₂ := eq28
       grind)
    | exact resolve eq200948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200948
  have eq201427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j0 := eq200952 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200952
  have eq201428 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq201427
  have eq201460 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  have eq201519 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq201428 eq8232
    | exact resolve eq8232 eq201428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8232
  have eq201522 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq201519 x
       have i₂ := eq927 sF1 x
       grind)
    | exact superpose eq927 eq201519
    | exact resolve eq201519 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq201519
  have eq201554 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq201460 eq150
    | exact resolve eq150 eq201460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq201460
  have eq201697 : (k y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq27925 eq201554
    | exact resolve eq201554 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201554
  have eq202568 : (τ (σ (M.op x y))) = (k y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq201428 eq201697
    | exact resolve eq201697 eq201428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201428 eq201697
  have eq202727 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by grind
  clear eq202568
  have eq202769 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq202727
    | exact resolve eq202727 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq202727
  have eq202786 : y = (k y y) ∨ x = y := by
    first
    | exact superpose eq27925 eq202769
    | exact resolve eq202769 eq27925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27925 eq202769
  have eq202916 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq202786
       grind)
    | exact superpose eq202786 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq202786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202786
  have eq202931 : y = (M.op y y) ∨ x = y := by grind
  clear eq202916
  have eq202951 : y = (M.op y y) := by
    first
    | (have r₁ := eq202931
       have r₂ := eq193960
       grind)
    | exact resolve eq202931 eq193960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193960 eq202931
  have eq203102 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq202951
       have i₂ := eq200716 X0
       grind)
    | exact superpose eq200716 eq202951
    | (have j1 := eq200716 X0
       grind)
    | exact resolve eq202951 eq200716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200716
  have eq203156 : (k y y) = (M.op y y) := by grind
  have eq203241 : y = (k y y) := by
    first
    | (have i₁ := eq203156
       have i₂ := eq202951
       grind)
    | exact superpose eq202951 eq203156
    | exact resolve eq203156 eq202951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202951 eq203156
  have eq203391 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq541 y
       have i₂ := eq203241
       grind)
    | exact superpose eq203241 eq541
    | (have j0 := eq541 y
       grind)
    | exact resolve eq541 eq203241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq203241
  have eq203408 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq203391
  have eq203425 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq203408
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq203408
    | exact resolve eq203408 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203408
  have eq203450 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28088 eq203425
    | exact resolve eq203425 eq28088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203425
  have eq204621 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f204621_14 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = y := by
      intro X0
      grind
    have f204621_15 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = y := by
      intro X0
      grind
    have f204621_24 : (σ (M.op x y)) ≠ (M.op X0 (σ (M.op x y))) := by grind
    have f204621_26 : x ≠ y := by grind
    have f204621_28 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f204621_15 X0
         grind)
      | (have r₁ := f204621_15 X0
         have r₂ := f204621_26
         grind)
      | exact resolve f204621_15 f204621_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204621_29 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
      intro X0
      first
      | (have j0 := f204621_14 X0
         grind)
      | (have r₁ := f204621_14 X0
         have r₂ := f204621_26
         grind)
      | exact resolve f204621_14 f204621_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204621_30 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
      intro X0
      first
      | (have i₁ := f204621_29 X0
         have i₂ := f204621_28 X0
         grind)
      | exact superpose f204621_28 f204621_29
      | exact resolve f204621_29 f204621_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204621_74 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
      first
      | (have i₁ := f204621_24
         have i₂ := f204621_30 X0
         grind)
      | exact superpose f204621_30 f204621_24
      | (have r₁ := f204621_24
         have r₂ := f204621_30 X0
         grind)
      | exact resolve f204621_24 f204621_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f204621_75 : False := by grind
    exact f204621_75
  clear eq201522 eq203102
  have eq204877 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq204621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204621
  have eq207534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq204877 eq28089
    | exact resolve eq28089 eq204877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204877
  have eq207613 : x = y := by
    first
    | (have r₁ := eq207534
       have r₂ := eq28
       grind)
    | exact resolve eq207534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207534
  have eq207665 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq207613
       grind)
    | exact superpose eq207613 eq25
    | exact resolve eq25 eq207613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq207613
  have eq208226 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28088 eq207665
    | exact resolve eq207665 eq28088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28088 eq207665
  have eq208317 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq208226
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq208226
    | exact resolve eq208226 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq208226
  have eq208488 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq208317 eq28089
    | exact resolve eq28089 eq208317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28089 eq208317
  have eq208604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq203450 eq208488
    | exact resolve eq208488 eq203450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203450 eq208488
  have eq208690 : False := by grind
  exact eq208690
