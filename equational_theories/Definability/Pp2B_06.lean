import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq44
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq82
    | exact resolve eq82 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq133 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq150 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq156 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq248 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq357 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq111
    | (have j0 := eq111 (σ X0)
       grind)
    | exact resolve eq111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq111 sF1
       grind)
    | exact superpose eq111 eq156
    | (have j1 := eq111 (σ (M.op x y))
       grind)
    | exact resolve eq156 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq396 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq67
    | exact resolve eq67 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq406 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq396 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq396
    | (have j0 := eq396 y x
       grind)
    | exact resolve eq396 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq396
    | (have j0 := eq396 (σ y) (σ x)
       grind)
    | exact resolve eq396 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 X0
       have i₂ := eq396 X0 X2
       grind)
    | exact superpose eq396 eq14
    | exact resolve eq14 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq448 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq69
    | exact resolve eq69 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq543 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq448 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq53 X1 X1 X0 X2
       grind)
    | exact superpose eq53 eq448
    | exact resolve eq448 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq448
  have eq750 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq112
    | (have j0 := eq112 X0
       grind)
    | exact resolve eq112 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq751 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq750
    | (have j0 := eq750 X0
       grind)
    | exact resolve eq750 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq1308 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq586 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq586
    | exact resolve eq586 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq1359 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1308 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq1308
    | exact resolve eq1308 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1376 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1308 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1308
    | (have j0 := eq1308 x y
       grind)
    | exact resolve eq1308 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1378 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq248 eq1308
    | exact resolve eq1308 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq4023 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq415
    | exact resolve eq415 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq4863 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq54
    | (have j1 := eq357 X0
       grind)
    | exact resolve eq54 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq5339 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq543 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq543
    | exact resolve eq543 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq26170 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1359 X0 y
       have i₂ := eq5339 X0
       grind)
    | exact superpose eq5339 eq1359
    | exact resolve eq1359 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339
  have eq26184 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4023 X0 X1
       have i₂ := eq1359 X0 X1
       grind)
    | exact superpose eq1359 eq4023
    | exact resolve eq4023 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359 eq4023
  have eq28980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28980
    | exact resolve eq28980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28980
  have eq28992 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28981
       have r₂ := eq28
       grind)
    | exact resolve eq28981 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28981
  have eq28994 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28992
    | exact resolve eq28992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28992
  have eq29011 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28994 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq28994
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq28994
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28994
       grind)
    | exact resolve eq12 eq28994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28994
  have eq29052 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29011
  have eq29082 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq29052
       have r₂ := eq27
       grind)
    | exact resolve eq29052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29052
  have eq29129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29082 eq85
    | exact resolve eq85 eq29082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29082
  have eq29138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq29129
  have eq29141 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq29138
       have r₂ := eq28
       grind)
    | exact resolve eq29138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29138
  have eq29170 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29141 eq252
    | exact resolve eq252 eq29141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29223 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29141 eq1308
    | exact resolve eq1308 eq29141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29141
  have eq29231 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29223
    | exact resolve eq29223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29223
  have eq29301 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq29231
       grind)
    | exact superpose eq29231 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq29231
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq29231
       grind)
    | exact resolve eq12 eq29231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29231
  have eq29342 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29301
  have eq29371 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29342
       have r₂ := eq19
       grind)
    | exact resolve eq29342 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29342
  have eq29415 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29371
       grind)
    | exact superpose eq29371 eq45
    | exact resolve eq45 eq29371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29371
  have eq29435 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq29415
    | exact resolve eq29415 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29415
  have eq29448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29435 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq29435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29448
    | exact resolve eq29448 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29448
  have eq29462 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29451
       have r₂ := eq28
       grind)
    | exact resolve eq29451 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29451
  have eq29464 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29462
    | exact resolve eq29462 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29462
  have eq29578 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29170 eq85
    | exact resolve eq85 eq29170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq29170
  have eq29590 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq29578
  have eq29618 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq29590
       grind)
    | exact superpose eq29590 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq29590
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq29590
       grind)
    | exact resolve eq12 eq29590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29590
  have eq29659 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29618
  have eq29688 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq29659
       have r₂ := eq19
       grind)
    | exact resolve eq29659 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29659
  have eq29731 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29688
       grind)
    | exact superpose eq29688 eq45
    | exact resolve eq45 eq29688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29688
  have eq29751 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq29731
    | exact resolve eq29731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29731
  have eq81662 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29464 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq29464
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq29464
       grind)
    | exact resolve eq12 eq29464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29464
  have eq81731 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81662
  have eq81777 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq81731
       have r₂ := eq27
       grind)
    | exact resolve eq81731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81731
  have eq87645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81777 eq29435
    | exact resolve eq29435 eq81777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29435 eq81777
  have eq87680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq87645
  have eq87711 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq87680
       have r₂ := eq28
       grind)
    | exact resolve eq87680 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87680
  have eq87812 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87711 eq1308
    | exact resolve eq1308 eq87711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87711
  have eq87855 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq87812
    | exact resolve eq87812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87812
  have eq87856 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq87855
  have eq88205 : (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq88219 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq751 y
       have i₂ := eq87856
       grind)
    | exact superpose eq87856 eq751
    | exact resolve eq751 eq87856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq88265 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1308 y y
       have i₂ := eq87856
       grind)
    | exact superpose eq87856 eq1308
    | exact resolve eq1308 eq87856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87856
  have eq88301 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88265
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88265
    | exact resolve eq88265 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88265
  have eq88358 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88301 eq28
    | exact resolve eq28 eq88301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88364 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88301 eq408
    | exact resolve eq408 eq88301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq88469 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq88364
    | exact resolve eq88364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88364
  have eq90314 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88469 eq54
    | exact resolve eq54 eq88469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90317 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88469 eq252
    | exact resolve eq252 eq88469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88469
  have eq92044 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88301 eq90314
    | exact resolve eq90314 eq88301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90314
  have eq92157 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq92044
  have eq92502 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88301 eq90317
    | exact resolve eq90317 eq88301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90317
  have eq92508 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq92502
  have eq92663 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92157 eq26184
    | exact resolve eq26184 eq92157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26184 eq92157
  have eq92676 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq92663
    | exact resolve eq92663 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92663
  have eq93015 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92508 eq29751
    | exact resolve eq29751 eq92508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29751 eq92508
  have eq93027 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq93015
  have eq93378 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88301 eq92676
    | exact resolve eq92676 eq88301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88301 eq92676
  have eq93472 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq93378
  have eq93935 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq93472 eq56
    | exact resolve eq56 eq93472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq93472
  have eq95163 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq88205
       grind)
    | exact superpose eq88205 eq45
    | exact resolve eq45 eq88205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq88205
  have eq111153 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4863 x
       have i₂ := eq88219
       grind)
    | exact superpose eq88219 eq4863
    | (have j0 := eq4863 x
       grind)
    | exact resolve eq4863 eq88219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863
  have eq111278 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111153
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq111153
    | exact resolve eq111153 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111153
  have eq111301 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111278
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq111278
    | exact resolve eq111278 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111278
  have eq111312 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq111301
    | exact resolve eq111301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111301
  have eq111313 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq111312
  have eq111318 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq111313
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq111313
    | exact resolve eq111313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111313
  have eq118511 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq111318 eq252
    | exact resolve eq252 eq111318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111318
  have eq118662 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq118511 eq50
    | exact resolve eq50 eq118511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq118511
  have eq118694 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq118662
    | exact resolve eq118662 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118662
  have eq120587 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq88219
       have i₂ := eq118694
       grind)
    | exact superpose eq118694 eq88219
    | exact resolve eq88219 eq118694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88219 eq118694
  have eq120595 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq120587
  have eq121085 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq120595 eq28
    | exact resolve eq28 eq120595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120595
  have eq136830 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1308 y y
       have i₂ := eq93027
       grind)
    | exact superpose eq93027 eq1308
    | exact resolve eq1308 eq93027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93027
  have eq136870 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136830
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq136830
    | exact resolve eq136830 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136830
  have eq136871 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq136870
  have eq136932 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq136871 eq30
    | exact resolve eq30 eq136871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq136951 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq136871 eq150
    | exact resolve eq150 eq136871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq137135 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq136871 eq93935
    | exact resolve eq93935 eq136871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93935 eq136871
  have eq137201 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq137135
  have eq137303 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156 eq136951
    | exact resolve eq136951 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq136951
  have eq137320 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq136932
    | exact resolve eq136932 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq136932
  have eq138003 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137320 eq1376
    | exact resolve eq1376 eq137320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq138190 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq140693 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137201 eq364
    | exact resolve eq364 eq137201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq137201
  have eq140834 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq140693
       have r₂ := eq88358
       grind)
    | exact resolve eq140693 eq88358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88358 eq140693
  have eq140845 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq140834
    | exact resolve eq140834 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq140834
  have eq161017 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137303 eq140845
    | exact resolve eq140845 eq137303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137303 eq140845
  have eq161022 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq161017
  have eq162643 : (M.op x (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26170 x
       have i₂ := eq138003
       grind)
    | exact superpose eq138003 eq26170
    | exact resolve eq26170 eq138003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26170 eq138003
  have eq162752 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq162643
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq162643
    | exact resolve eq162643 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq162643
  have eq176333 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq162752 eq1308
    | exact resolve eq1308 eq162752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq162752
  have eq176389 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1378 eq176333
    | exact resolve eq176333 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378 eq176333
  have eq187625 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq137320 eq176389
    | exact resolve eq176389 eq137320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137320 eq176389
  have eq187790 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq187625
       have r₂ := eq138190
       grind)
    | exact resolve eq187625 eq138190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187625
  have eq187799 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq187790
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq187790
    | exact resolve eq187790 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187790
  have eq187846 : y = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq252 y
       have i₂ := eq187799
       grind)
    | exact superpose eq187799 eq252
    | exact resolve eq252 eq187799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq187799
  have eq188994 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq187846 eq161022
    | exact resolve eq161022 eq187846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161022 eq187846
  have eq189003 : x = y ∨ x = (M.op x y) := by grind
  clear eq188994
  have eq189008 : x = (M.op x y) := by
    first
    | (have r₁ := eq189003
       have r₂ := eq138190
       grind)
    | exact resolve eq189003 eq138190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138190 eq189003
  have eq189025 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq189008 eq21
    | exact resolve eq21 eq189008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq189078 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq189008 eq406
    | exact resolve eq406 eq189008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq189401 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq189078
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq189078
    | exact resolve eq189078 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq189078
  have eq189449 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq189025
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq189025
    | exact resolve eq189025 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189025
  have eq189453 : x = (M.op y y) := by
    first
    | exact superpose eq189008 eq189401
    | exact resolve eq189401 eq189008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189008 eq189401
  have eq189458 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq189449 eq27
    | exact resolve eq27 eq189449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq189678 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq189449 eq121085
    | (have r₁ := eq121085
       have r₂ := eq189449
       grind)
    | exact resolve eq121085 eq189449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121085
  have eq189746 : x = y := by grind
  clear eq189678
  have eq189895 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq189746
       grind)
    | exact superpose eq189746 eq25
    | exact resolve eq25 eq189746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq190431 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq189895
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq189895
    | exact resolve eq189895 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189895
  have eq190614 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq189449 eq190431
    | exact resolve eq190431 eq189449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190431
  have eq192098 : x = (M.op x x) := by
    first
    | (have i₁ := eq189453
       have i₂ := eq189746
       grind)
    | exact superpose eq189746 eq189453
    | exact resolve eq189453 eq189746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189453 eq189746
  have eq192112 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95163
       have i₂ := eq192098
       grind)
    | exact superpose eq192098 eq95163
    | exact resolve eq95163 eq192098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95163 eq192098
  have eq192301 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190614 eq192112
    | exact resolve eq192112 eq190614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192112
  have eq192338 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq189449 eq192301
    | exact resolve eq192301 eq189449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192301
  have eq192353 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq192338
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq192338
    | exact resolve eq192338 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq192338
  have eq192363 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq189449 eq192353
    | exact resolve eq192353 eq189449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192353
  have eq192366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq189449 eq192363
    | exact resolve eq192363 eq189449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189449 eq192363
  have eq192368 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq192366
       have r₂ := eq28
       grind)
    | exact resolve eq192366 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192366
  have eq192374 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq190614 eq189458
    | exact resolve eq189458 eq190614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189458 eq190614
  have eq193262 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq192374 eq12
    | exact resolve eq12 eq192374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192374
  have eq193343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq193262
  have eq193381 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq193343
       have r₂ := eq28
       grind)
    | exact resolve eq193343 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193343
  have eq193422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq192368 eq193381
    | exact resolve eq193381 eq192368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192368 eq193381
  have eq193441 : False := by grind
  exact eq193441

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq36
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq64
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq56
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq74
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq597 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq611 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq603
    | (have j0 := eq603 X0 X1
       grind)
    | exact resolve eq603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq3335 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq460
    | exact resolve eq460 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq460
  have eq3363 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3335
    | (have j0 := eq3335 (σ y) (σ x)
       grind)
    | exact resolve eq3335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3784 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq611 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq611
    | (have j0 := eq611 (τ X0)
       grind)
    | exact resolve eq611 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq611
  have eq3805 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3784 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3784
    | (have j0 := eq3784 X0
       grind)
    | exact resolve eq3784 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq3818 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3805 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3805
    | (have j0 := eq3805 X0
       grind)
    | exact resolve eq3805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq23936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq23937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23936
    | exact resolve eq23936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23936
  have eq23948 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23937
       have r₂ := eq28
       grind)
    | exact resolve eq23937 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23937
  have eq23975 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23948 eq3335
    | exact resolve eq3335 eq23948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25291 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23975 eq23948
    | exact resolve eq23948 eq23975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23948 eq23975
  have eq25326 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq25291
  have eq25341 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25326 eq50
    | exact resolve eq50 eq25326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25326
  have eq25370 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25341
    | exact resolve eq25341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25341
  have eq25400 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3335 x y
       have i₂ := eq25370
       grind)
    | exact superpose eq25370 eq3335
    | exact resolve eq3335 eq25370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq27150 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25370
       have i₂ := eq25400
       grind)
    | exact superpose eq25400 eq25370
    | exact resolve eq25370 eq25400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25370 eq25400
  have eq27187 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27150
  have eq27194 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq27187
       grind)
    | exact superpose eq27187 eq67
    | exact resolve eq67 eq27187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq27203 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq27204 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq27187
       grind)
    | exact superpose eq27187 eq50
    | exact resolve eq50 eq27187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq27187
  have eq27235 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27204
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27204
    | exact resolve eq27204 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27204
  have eq27237 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27194
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27194
    | exact resolve eq27194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27194
  have eq27242 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27235 eq246
    | exact resolve eq246 eq27235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq27248 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27235 eq3363
    | exact resolve eq3363 eq27235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq27299 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq27248
    | exact resolve eq27248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248
  have eq28768 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27299 eq27242
    | exact resolve eq27242 eq27299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27242 eq27299
  have eq28806 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq28768
  have eq28811 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27235 eq28806
    | exact resolve eq28806 eq27235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27235 eq28806
  have eq28841 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28811
  have eq28845 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28841 eq76
    | exact resolve eq76 eq28841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq28841
  have eq28888 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq28845
    | exact resolve eq28845 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28845
  have eq31407 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27237 eq56
    | exact resolve eq56 eq27237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31426 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27237 eq3818
    | (have j0 := eq3818 (σ x)
       grind)
    | exact resolve eq3818 eq27237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27237
  have eq31439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq31426
    | exact resolve eq31426 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31426
  have eq31440 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31439
  have eq31449 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq31407
    | exact resolve eq31407 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31407
  have eq31514 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31440
  have eq32483 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31514 eq56
    | exact resolve eq56 eq31514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31514
  have eq32534 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq32483
    | exact resolve eq32483 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32483
  have eq32697 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq31449
       have i₂ := eq32534
       grind)
    | exact superpose eq32534 eq31449
    | exact resolve eq31449 eq32534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31449 eq32534
  have eq32721 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32697
  have eq32745 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq32721 eq28
    | exact resolve eq28 eq32721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32721
  have eq37772 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3818 x
       have i₂ := eq28888
       grind)
    | exact superpose eq28888 eq3818
    | (have j0 := eq3818 x
       grind)
    | exact resolve eq3818 eq28888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq37791 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37772
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37772
    | exact resolve eq37772 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37772
  have eq37792 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37791
  have eq38956 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37792
  have eq39376 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28888
       have i₂ := eq38956
       grind)
    | exact superpose eq38956 eq28888
    | exact resolve eq28888 eq38956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28888 eq38956
  have eq39402 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39376
  have eq39427 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39402 eq30
    | exact resolve eq30 eq39402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39402
  have eq39698 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq39427
    | exact resolve eq39427 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39427
  have eq39699 : x = (M.op x y) ∨ x = y := by grind
  clear eq39698
  have eq39700 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39699 eq21
    | exact resolve eq21 eq39699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39699
  have eq39917 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39700
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39700
    | exact resolve eq39700 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39700
  have eq39918 : x = y := by
    first
    | (have r₁ := eq39917
       have r₂ := eq32745
       grind)
    | exact resolve eq39917 eq32745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32745 eq39917
  have eq40187 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq39918
       grind)
    | exact superpose eq39918 eq19
    | exact resolve eq19 eq39918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40188 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39918
       grind)
    | exact superpose eq39918 eq25
    | exact resolve eq25 eq39918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq40318 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27203
       have i₂ := eq39918
       grind)
    | exact superpose eq39918 eq27203
    | exact resolve eq27203 eq39918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27203 eq39918
  have eq40413 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40188
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40188
    | exact resolve eq40188 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40188
  have eq40416 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40413 eq27
    | exact resolve eq27 eq40413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40413
  have eq41225 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq43862 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq615 x x
       have i₂ := eq40318
       grind)
    | exact superpose eq40318 eq615
    | (have j0 := eq615 x x
       grind)
    | exact resolve eq615 eq40318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq40318
  have eq43871 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43862
  have eq43872 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43871
  have eq43884 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43872
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43872
    | exact resolve eq43872 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43872
  have eq43906 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40416 eq43884
    | exact resolve eq43884 eq40416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40416 eq43884
  have eq43907 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43906
  have eq43926 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq43907 eq28
    | exact resolve eq28 eq43907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq44008 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq43907 eq41225
    | exact resolve eq41225 eq43907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41225 eq43907
  have eq45281 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq44008 eq56
    | exact resolve eq56 eq44008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq44008
  have eq45341 : x = (k x x) := by
    first
    | exact superpose eq29 eq45281
    | exact resolve eq45281 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45281
  have eq45380 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq45341
       grind)
    | exact superpose eq45341 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq45341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45341
  have eq45381 : x = (M.op x x) := by grind
  clear eq45380
  have eq45396 : x = (M.op x y) := by
    first
    | (have i₁ := eq45381
       have i₂ := eq40187
       grind)
    | exact superpose eq40187 eq45381
    | exact resolve eq45381 eq40187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40187 eq45381
  have eq45435 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq45396 eq21
    | exact resolve eq21 eq45396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45396
  have eq45713 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45435
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45435
    | exact resolve eq45435 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45435
  have eq45792 : False := by grind
  exact eq45792

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq85 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (σ (k x (k y y))) = (k (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq36
    | exact resolve eq36 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq249 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq248 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq248
    | exact resolve eq248 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq418 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq438 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq561 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq566 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq566 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq566 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq582 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq573
    | (have j0 := eq573 X0 X1
       grind)
    | exact resolve eq573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq3337 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq431
    | exact resolve eq431 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq3366 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3337
    | (have j0 := eq3337 (σ y) (σ x)
       grind)
    | exact resolve eq3337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3516 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq436 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq436
    | exact resolve eq436 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq3548 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq438 sF2 X1 x
       have i₂ := eq56 sF2 sF2
       grind)
    | exact superpose eq56 eq438
    | exact resolve eq438 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq3566 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3516 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3516
    | exact resolve eq3516 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516
  have eq3697 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3548 sF4 sF4
       have i₂ := eq54 sF4
       grind)
    | exact superpose eq54 eq3548
    | exact resolve eq3548 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq3719 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3697 eq14
    | exact resolve eq14 eq3697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq3863 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq427 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq427
    | exact resolve eq427 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq4022 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq434 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq434
    | exact resolve eq434 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq4137 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3719 sF2
       have i₂ := eq54 sF2
       grind)
    | exact superpose eq54 eq3719
    | exact resolve eq3719 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq5186 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7128 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7171 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq7587 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq582
  have eq7784 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7587 X0
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq7587
    | (have j0 := eq7587 X0
       grind)
    | exact resolve eq7587 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7587
  have eq7871 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7784 X0
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq7784
    | (have j0 := eq7784 X0
       grind)
    | exact resolve eq7784 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq7784
  have eq7872 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7871
  have eq12508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12508
    | exact resolve eq12508 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12508
  have eq12520 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12509
       have r₂ := eq28
       grind)
    | exact resolve eq12509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12509
  have eq12522 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12520
    | exact resolve eq12520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12520
  have eq12530 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  have eq12550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12522 eq3337
    | exact resolve eq3337 eq12522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522
  have eq12551 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12550
    | exact resolve eq12550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550
  have eq12554 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12530
    | exact resolve eq12530 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12530
  have eq12562 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12551
  have eq12586 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12562
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12562
    | exact resolve eq12562 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12562
  have eq13041 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12586
       grind)
    | exact superpose eq12586 eq45
    | exact resolve eq45 eq12586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12586
  have eq13065 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13041
    | exact resolve eq13041 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13041
  have eq13368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13065 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13065
  have eq13369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13368
    | exact resolve eq13368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13368
  have eq13380 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13369
       have r₂ := eq28
       grind)
    | exact resolve eq13369 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13369
  have eq13382 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13380
    | exact resolve eq13380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13380
  have eq13383 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13382
  have eq13704 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13383 eq3337
    | exact resolve eq3337 eq13383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13383
  have eq13705 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13704
    | exact resolve eq13704 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13704
  have eq13706 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13705
  have eq13728 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13706
  have eq14843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12554 eq84
    | exact resolve eq84 eq12554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12554
  have eq14860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14843
  have eq14864 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14860
       have r₂ := eq28
       grind)
    | exact resolve eq14860 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860
  have eq14873 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14864
  have eq14897 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14873
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14873
    | exact resolve eq14873 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14873
  have eq15013 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq14897
       grind)
    | exact superpose eq14897 eq45
    | exact resolve eq45 eq14897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14897
  have eq15040 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15013
    | exact resolve eq15013 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15013
  have eq15313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15040 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq15040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15313
    | exact resolve eq15313 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313
  have eq15329 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15318
       have r₂ := eq28
       grind)
    | exact resolve eq15318 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15318
  have eq15331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15329
    | exact resolve eq15329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15329
  have eq15332 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15331
  have eq15410 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15332
  have eq15438 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15410
    | exact resolve eq15410 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15410
  have eq15526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15438 eq15040
    | exact resolve eq15040 eq15438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15040 eq15438
  have eq15535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15526
  have eq15544 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15535
       have r₂ := eq28
       grind)
    | exact resolve eq15535 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15535
  have eq15546 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15544 eq28
    | exact resolve eq28 eq15544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15547 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15544 eq52
    | exact resolve eq52 eq15544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq15637 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15547
    | (have j0 := eq15547 (σ x)
       grind)
    | exact resolve eq15547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15547
  have eq15691 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15637 eq14
    | exact resolve eq14 eq15637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15637
  have eq16053 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15691 eq250
    | exact resolve eq250 eq15691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq16153 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16053 eq250
    | exact resolve eq250 eq16053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq16053
  have eq18317 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16153 sF2
       have i₂ := eq54 sF2
       grind)
    | exact superpose eq54 eq16153
    | exact resolve eq16153 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153
  have eq18374 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15544 eq18317
    | exact resolve eq18317 eq15544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18317
  have eq18424 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18374
  have eq18434 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq18424
    | exact resolve eq18424 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18424
  have eq18438 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18434 eq245
    | exact resolve eq245 eq18434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq18456 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  have eq18457 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18434 eq54
    | exact resolve eq54 eq18434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq18462 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18434 eq254
    | exact resolve eq254 eq18434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq18497 : (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3366 eq18456
    | exact resolve eq18456 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366 eq18456
  have eq18656 : (k (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq18438
  have eq18719 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18457 eq3337
    | exact resolve eq3337 eq18457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337 eq18457
  have eq18727 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15544 eq18462
    | exact resolve eq18462 eq15544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq18746 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18727
  have eq18998 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18746 eq105
    | exact resolve eq105 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18746
  have eq19044 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq18998
    | exact resolve eq18998 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18998
  have eq19099 : (σ (k x y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19044
       grind)
    | exact superpose eq19044 eq102
    | exact resolve eq102 eq19044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq19118 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19044
       grind)
    | exact superpose eq19044 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19119 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq19118
  have eq19145 : (k (σ x) (σ y)) = (k (σ x) (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19099
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq19099
    | exact resolve eq19099 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19099
  have eq19163 : (M.op y y) = (k y y) ∨ y = (M.op x y) := by grind
  have eq19620 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15544 eq18497
    | exact resolve eq18497 eq15544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15544 eq18497
  have eq19642 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19620
  have eq19819 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18719 eq4137
    | exact resolve eq4137 eq18719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137 eq18719
  have eq19968 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19642 eq105
    | exact resolve eq105 eq19642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq21331 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18434 eq19968
    | exact resolve eq19968 eq18434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19968
  have eq21385 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq21331
  have eq21411 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19044
       have i₂ := eq21385
       grind)
    | exact superpose eq21385 eq19044
    | exact resolve eq19044 eq21385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19044
  have eq21412 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19163
       have i₂ := eq21385
       grind)
    | exact superpose eq21385 eq19163
    | exact resolve eq19163 eq21385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19163 eq21385
  have eq21432 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq21412
  have eq21433 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq21411
  have eq21491 : (σ (k y y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21433 eq85
    | exact resolve eq85 eq21433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq21433
  have eq21542 : (k (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21491
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq21491
    | exact resolve eq21491 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq21491
  have eq21669 : y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq244
       have i₂ := eq21432
       grind)
    | exact superpose eq21432 eq244
    | exact resolve eq244 eq21432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq21432
  have eq21805 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21669 eq7128
    | exact resolve eq7128 eq21669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128 eq21669
  have eq22016 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21542 eq18656
    | exact resolve eq18656 eq21542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18656 eq21542
  have eq22025 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq22016
  have eq22365 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22025 eq19642
    | exact resolve eq19642 eq22025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22025
  have eq22389 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq22365
  have eq24202 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22389 eq19819
    | exact resolve eq19819 eq22389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19819 eq22389
  have eq24246 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq24202
  have eq25128 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24246 eq12
    | (have j0 := eq12 (σ x) (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24246
       grind)
    | exact resolve eq12 eq24246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24246
  have eq25154 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq25128
       have r₂ := eq18434
       grind)
    | exact resolve eq25128 eq18434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18434 eq25128
  have eq25156 : (σ x) = (σ y) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25154
       have i₂ := eq56 sF3 sF3
       grind)
    | exact superpose eq56 eq25154
    | exact resolve eq25154 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25154
  have eq25157 : (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25156
       have i₂ := eq56 sF3 sF3
       grind)
    | exact superpose eq56 eq25156
    | exact resolve eq25156 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25156
  have eq28176 : y = (M.op (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21805
       have i₂ := eq19119
       grind)
    | exact superpose eq19119 eq21805
    | exact resolve eq21805 eq19119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21805
  have eq28209 : y = (M.op (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) := by grind
  clear eq28176
  have eq30315 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4022 y x y
       have i₂ := eq19119
       grind)
    | exact superpose eq19119 eq4022
    | exact resolve eq4022 eq19119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq36671 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19642 eq19145
    | exact resolve eq19145 eq19642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19145 eq19642
  have eq36691 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq36671
  have eq38702 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30315 X0
       have i₂ := eq19119
       grind)
    | exact superpose eq19119 eq30315
    | exact resolve eq30315 eq19119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19119 eq30315
  have eq38774 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq38702 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38702
  have eq274065 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25157 eq36691
    | exact resolve eq36691 eq25157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25157 eq36691
  have eq274076 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq274065
  have eq274107 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq274076 eq84
    | exact resolve eq84 eq274076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq274076
  have eq274146 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq274107
  have eq274165 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq274146
       have r₂ := eq15546
       grind)
    | exact resolve eq274146 eq15546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15546 eq274146
  have eq274375 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38774 y
       have i₂ := eq274165
       grind)
    | exact superpose eq274165 eq38774
    | exact resolve eq38774 eq274165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38774 eq274165
  have eq274445 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq274375
  have eq274491 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq274445
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq274445
    | exact resolve eq274445 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274445
  have eq274492 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq274491
  have eq274640 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq274492 eq13728
    | (have r₁ := eq13728
       have r₂ := eq274492
       grind)
    | exact resolve eq13728 eq274492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13728 eq274492
  have eq275745 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq274640
  have eq275746 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq275745
  have eq276042 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq275746 eq28209
    | exact resolve eq28209 eq275746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28209 eq275746
  have eq277075 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) := by grind
  clear eq276042
  have eq277370 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq277075
    | exact resolve eq277075 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq277075
  have eq277468 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq277370
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq277370
    | exact resolve eq277370 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277370
  have eq277469 : y = (M.op x y) := by grind
  clear eq277468
  have eq277482 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq277469 eq21
    | exact resolve eq21 eq277469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq277489 : y ≠ y ∨ x = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq277469 eq109
    | (have r₁ := eq109
       have r₂ := eq277469
       grind)
    | exact resolve eq109 eq277469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq277645 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq277469 eq3566
    | exact resolve eq3566 eq277469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq277660 : x = (M.op y y) ∨ (k x y) = (M.op y y) := by grind
  clear eq277489
  have eq277805 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq277482
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq277482
    | exact resolve eq277482 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277482
  have eq277809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq277805 eq27
    | exact resolve eq27 eq277805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278616 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq3863 x
       have i₂ := eq277645
       grind)
    | exact superpose eq277645 eq3863
    | exact resolve eq3863 eq277645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863 eq277645
  have eq278671 : (M.op (M.op x x) (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | exact superpose eq277469 eq278616
    | exact resolve eq278616 eq277469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278616
  have eq278674 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq278671
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq278671
    | exact resolve eq278671 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq278671
  have eq279769 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 (M.op x x)
       have i₂ := eq278674
       grind)
    | exact superpose eq278674 eq14
    | exact resolve eq14 eq278674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278674
  have eq288472 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq7171 x (M.op y y)
       have i₂ := eq279769 x
       grind)
    | exact superpose eq279769 eq7171
    | exact resolve eq7171 eq279769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7171 eq279769
  have eq288546 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq288472
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq288472
    | exact resolve eq288472 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq288472
  have eq288549 : y = (M.op y y) := by
    first
    | exact superpose eq277469 eq288546
    | exact resolve eq288546 eq277469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277469 eq288546
  have eq288618 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7872 y
       have i₂ := eq288549
       grind)
    | exact superpose eq288549 eq7872
    | exact resolve eq7872 eq288549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7872
  have eq288653 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq288618
  have eq288664 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq288653
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq288653
    | exact resolve eq288653 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288653
  have eq288677 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq277805 eq288664
    | exact resolve eq288664 eq277805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288664
  have eq512258 : x = y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq277660
       have i₂ := eq288549
       grind)
    | exact superpose eq288549 eq277660
    | exact resolve eq277660 eq288549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277660
  have eq512259 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq512258
       have i₂ := eq288549
       grind)
    | exact superpose eq288549 eq512258
    | exact resolve eq512258 eq288549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288549 eq512258
  have eq512310 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5186 y
       have i₂ := eq512259
       grind)
    | exact superpose eq512259 eq5186
    | (have j0 := eq5186 y
       grind)
    | exact resolve eq5186 eq512259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq512259
  have eq512338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq512310
  have eq512366 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq512338
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq512338
    | exact resolve eq512338 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512338
  have eq512417 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq512366
    | exact resolve eq512366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq512366
  have eq512464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq277805 eq512417
    | exact resolve eq512417 eq277805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512417
  have eq512507 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq512464
       have r₂ := eq28
       grind)
    | exact resolve eq512464 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512464
  have eq512536 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq512507
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq512507
    | exact resolve eq512507 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512507
  have eq512558 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq277805 eq512536
    | exact resolve eq512536 eq277805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512536
  have eq512578 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq288677 eq512558
    | exact resolve eq512558 eq288677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512558
  have eq512952 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq512578 eq277809
    | exact resolve eq277809 eq512578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512578
  have eq512982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq288677 eq512952
    | exact resolve eq512952 eq288677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512952
  have eq513083 : x = y := by
    first
    | (have r₁ := eq512982
       have r₂ := eq28
       grind)
    | exact resolve eq512982 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512982
  have eq513271 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq513083
       grind)
    | exact superpose eq513083 eq25
    | exact resolve eq25 eq513083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq513083
  have eq513974 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq277805 eq513271
    | exact resolve eq513271 eq277805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277805 eq513271
  have eq514213 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq513974
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq513974
    | exact resolve eq513974 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq513974
  have eq516125 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq514213 eq277809
    | exact resolve eq277809 eq514213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277809 eq514213
  have eq516155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq288677 eq516125
    | exact resolve eq516125 eq288677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288677 eq516125
  have eq516256 : False := by grind
  exact eq516256

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq247 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq252 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq247
    | exact resolve eq247 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq409 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq446 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op X0 X1) X1
       have i₂ := eq56 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq545 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq54
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq54 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq557 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq545 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq3288 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq422
    | exact resolve eq422 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3316 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3288
    | (have j0 := eq3288 (σ y) (σ x)
       grind)
    | exact resolve eq3288 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3367 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3316 eq14
    | exact resolve eq14 eq3316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq3471 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq427 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq427
    | exact resolve eq427 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq3488 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3471 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3471
    | exact resolve eq3471 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471
  have eq3806 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3367 sF3
       have i₂ := eq54 sF3
       grind)
    | exact superpose eq54 eq3367
    | exact resolve eq3367 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3832 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq3806 eq14
    | exact resolve eq14 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3851 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq418 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq3891 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq420 (M.op sF3 x) x
       have i₂ := eq56 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq56 eq420
    | exact resolve eq420 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq4065 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq425 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq425
    | exact resolve eq425 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq6690 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq409
    | exact resolve eq409 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6733 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq409
    | exact resolve eq409 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq7513 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq424 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq54 (M.op X1 X2)
       grind)
    | exact superpose eq54 eq424
    | exact resolve eq424 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq20570 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4065 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq4065
    | exact resolve eq4065 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4065
  have eq26059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26059
    | exact resolve eq26059 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26059
  have eq26071 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26060
       have r₂ := eq28
       grind)
    | exact resolve eq26060 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26060
  have eq26088 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26071 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26071
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26071
       grind)
    | exact resolve eq12 eq26071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26108 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26088
  have eq26109 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26108
  have eq26119 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26109 eq82
    | exact resolve eq82 eq26109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26109
  have eq26133 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26119
  have eq26164 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26133
  have eq26199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq26164
    | exact resolve eq26164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26164
  have eq27618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26199 eq82
    | exact resolve eq82 eq26199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq26199
  have eq27635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27618
  have eq27639 : y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq27635
       have r₂ := eq28
       grind)
    | exact resolve eq27635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27635
  have eq27673 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3288 x y
       have i₂ := eq27639
       grind)
    | exact superpose eq27639 eq3288
    | exact resolve eq3288 eq27639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29535 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27639
       have i₂ := eq27673
       grind)
    | exact superpose eq27673 eq27639
    | exact resolve eq27639 eq27673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27639 eq27673
  have eq29579 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29535
  have eq29609 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq29579
       grind)
    | exact superpose eq29579 eq56
    | exact resolve eq56 eq29579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29579
  have eq29630 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29609
  have eq29661 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq29674 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq29630
       grind)
    | exact superpose eq29630 eq56
    | exact resolve eq56 eq29630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29630
  have eq29702 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29661
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29661
    | exact resolve eq29661 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29661
  have eq30188 : x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq252 x
       have i₂ := eq29674
       grind)
    | exact superpose eq29674 eq252
    | exact resolve eq252 eq29674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29674
  have eq30225 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29702
       grind)
    | exact superpose eq29702 eq45
    | exact resolve eq45 eq29702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29702
  have eq30259 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq30225
    | exact resolve eq30225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30225
  have eq30354 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq30188
       grind)
    | exact superpose eq30188 eq45
    | exact resolve eq45 eq30188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq30188
  have eq30389 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq30354
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30354
    | exact resolve eq30354 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30354
  have eq30425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30259 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq30259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq30425
    | exact resolve eq30425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30425
  have eq30445 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq30434
       have r₂ := eq28
       grind)
    | exact resolve eq30434 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30434
  have eq30468 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30389 eq30259
    | exact resolve eq30259 eq30389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30389
  have eq30476 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq30468
  have eq546293 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30445 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq30445
       grind)
    | exact resolve eq12 eq30445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30445
  have eq546354 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq546293
  have eq546355 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq546354
  have eq547191 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq546355 eq30259
    | exact resolve eq30259 eq546355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30259 eq546355
  have eq547247 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq547191
  have eq547477 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq547247 eq20570
    | exact resolve eq20570 eq547247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547247
  have eq547482 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq547477
    | exact resolve eq547477 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547477
  have eq547500 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq547482 eq28
    | exact resolve eq28 eq547482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547482
  have eq547651 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq547500
       have r₂ := eq30476
       grind)
    | exact resolve eq547500 eq30476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30476 eq547500
  have eq547653 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq547651 eq27
    | exact resolve eq27 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq547654 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq547651 eq30
    | exact resolve eq30 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq547751 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq547651 eq3832
    | exact resolve eq3832 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832
  have eq547752 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq547651 eq3891
    | exact resolve eq3891 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq548400 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq547654
    | exact resolve eq547654 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq547654
  have eq548604 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq548400 eq3488
    | exact resolve eq3488 eq548400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq553604 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq3851 x
       have i₂ := eq548604
       grind)
    | exact superpose eq548604 eq3851
    | exact resolve eq3851 eq548604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq553732 : (M.op (M.op x x) (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | exact superpose eq548400 eq553604
    | exact resolve eq553604 eq548400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553604
  have eq553744 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq553732
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq553732
    | exact resolve eq553732 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553732
  have eq554050 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq20570 y (M.op x x)
       have i₂ := eq553744
       grind)
    | exact superpose eq553744 eq20570
    | exact resolve eq20570 eq553744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20570 eq553744
  have eq554053 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq554050
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq554050
    | exact resolve eq554050 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq554050
  have eq554077 : y = (M.op y y) := by
    first
    | exact superpose eq548400 eq554053
    | exact resolve eq554053 eq548400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548400 eq554053
  have eq554204 : y = (k y y) := by
    first
    | (have i₁ := eq252 y
       have i₂ := eq554077
       grind)
    | exact superpose eq554077 eq252
    | exact resolve eq252 eq554077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq554420 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq557 y
       have i₂ := eq554204
       grind)
    | exact superpose eq554204 eq557
    | (have j0 := eq557 y
       grind)
    | exact resolve eq557 eq554204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq554204
  have eq554486 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq554420
  have eq554523 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq554486
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq554486
    | exact resolve eq554486 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554486
  have eq554584 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq547651 eq554523
    | exact resolve eq554523 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554523
  have eq597151 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq554584 eq547751
    | exact resolve eq547751 eq554584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547751
  have eq597233 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq597151 eq446
    | exact resolve eq446 eq597151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597151
  have eq760658 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op X1 X0) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq547752 eq422
    | exact resolve eq422 eq547752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq793707 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq547752 eq597233
    | exact resolve eq597233 eq547752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597233
  have eq885569 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op X1 X0) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq793707 eq760658
    | exact resolve eq760658 eq793707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760658
  have eq891576 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq885569 eq6733
    | exact resolve eq6733 eq885569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733 eq885569
  have eq891846 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq547752 eq891576
    | exact resolve eq891576 eq547752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547752 eq891576
  have eq892305 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq793707 eq891846
    | exact resolve eq891846 eq793707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793707 eq891846
  have eq893221 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq892305 eq14
    | exact resolve eq14 eq892305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892305
  have eq1086105 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq893221 eq7513
    | exact resolve eq7513 eq893221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7513 eq893221
  have eq1298104 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1086105 X1 X2
       have i₂ := eq446 X1 X2 X0
       grind)
    | (have i₁ := eq1086105 X1 X1
       have i₂ := eq446 X1 X1 X1
       grind)
    | exact superpose eq446 eq1086105
    | exact resolve eq1086105 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086105
  have eq1461989 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1298104 X0 X0 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq6690 X0 X1
       grind)
    | exact superpose eq6690 eq1298104
    | exact resolve eq1298104 eq6690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6690 eq1298104
  have eq1531763 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1461989 X1 X2 X1
       have i₂ := eq446 X1 X2 X0
       grind)
    | (have i₁ := eq1461989 X1 X1 X2
       have i₂ := eq446 X1 X1 X2
       grind)
    | exact superpose eq446 eq1461989
    | exact resolve eq1461989 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq1461989
  have eq1541936 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq26071 eq1531763
    | exact resolve eq1531763 eq26071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26071 eq1531763
  have eq1542925 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1541936 x
       have i₂ := eq3288 sF3 x
       grind)
    | exact superpose eq3288 eq1541936
    | exact resolve eq1541936 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288 eq1541936
  have eq1543974 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq547651 eq1542925
    | exact resolve eq1542925 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542925
  have eq1544568 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq554584 eq1543974
    | exact resolve eq1543974 eq554584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543974
  have eq1544851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq547653 eq1544568
    | exact resolve eq1544568 eq547653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544568
  have eq1544981 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1544851
       have r₂ := eq28
       grind)
    | exact resolve eq1544851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544851
  have eq1545033 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq547651 eq1544981
    | exact resolve eq1544981 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544981
  have eq1545067 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq554584 eq1545033
    | exact resolve eq1545033 eq554584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545033
  have eq1545096 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1545067
       have i₂ := eq548604
       grind)
    | exact superpose eq548604 eq1545067
    | exact resolve eq1545067 eq548604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548604 eq1545067
  have eq1545122 : y = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1545096
       have i₂ := eq554077
       grind)
    | exact superpose eq554077 eq1545096
    | exact resolve eq1545096 eq554077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545096
  have eq1545275 : x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq1545122
       grind)
    | exact superpose eq1545122 eq56
    | exact resolve eq56 eq1545122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1545122
  have eq1545418 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1545275
       have i₂ := eq554077
       grind)
    | exact superpose eq554077 eq1545275
    | exact resolve eq1545275 eq554077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554077 eq1545275
  have eq1545419 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1545418
  have eq1545960 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1545419 eq547653
    | exact resolve eq547653 eq1545419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545419
  have eq1545999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq554584 eq1545960
    | exact resolve eq1545960 eq554584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545960
  have eq1546151 : x = y := by
    first
    | (have r₁ := eq1545999
       have r₂ := eq28
       grind)
    | exact resolve eq1545999 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545999
  have eq1546465 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1546151
       grind)
    | exact superpose eq1546151 eq25
    | exact resolve eq25 eq1546151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1546151
  have eq1547760 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq547651 eq1546465
    | exact resolve eq1546465 eq547651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547651 eq1546465
  have eq1548200 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1547760
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1547760
    | exact resolve eq1547760 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1547760
  have eq1549008 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1548200 eq547653
    | exact resolve eq547653 eq1548200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547653 eq1548200
  have eq1549044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq554584 eq1549008
    | exact resolve eq1549008 eq554584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554584 eq1549008
  have eq1549196 : False := by grind
  exact eq1549196

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq82
    | exact resolve eq82 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq109 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq206 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq158
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq208 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq206
  have eq420 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq560 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq50
    | (have j1 := eq70 X0 X0
       grind)
    | exact resolve eq50 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq574 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq3395 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq420 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq420
    | exact resolve eq420 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq3421 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3395 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3395
    | (have j0 := eq3395 y x
       grind)
    | exact resolve eq3395 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3742 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq574 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq574
    | (have j0 := eq574 (τ X0)
       grind)
    | exact resolve eq574 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq574
  have eq3763 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3742 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3742
    | (have j0 := eq3742 X0
       grind)
    | exact resolve eq3742 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742
  have eq3775 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3763 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3763
    | (have j0 := eq3763 X0
       grind)
    | exact resolve eq3763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763
  have eq4016 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq423 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq423
    | exact resolve eq423 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq20538 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4016 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4016
    | exact resolve eq4016 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq4016
  have eq26170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq26171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26170
    | exact resolve eq26170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26170
  have eq26182 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26171
       have r₂ := eq28
       grind)
    | exact resolve eq26171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26171
  have eq26199 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26182 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26182
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26182
       grind)
    | exact resolve eq12 eq26182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26182
  have eq26219 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26199
  have eq26220 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26219
  have eq26229 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26220 eq60
    | exact resolve eq60 eq26220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26220
  have eq26254 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq26229
    | exact resolve eq26229 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26229
  have eq26257 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq26254
       have r₂ := eq12 x y
       grind)
    | exact resolve eq26254 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26254
  have eq26277 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq26257
  have eq26981 : (τ (σ x)) = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26277 eq60
    | exact resolve eq60 eq26277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq26277
  have eq27005 : x = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq26981
    | exact resolve eq26981 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26981
  have eq27006 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq27005
  have eq27310 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq27006
       grind)
    | exact superpose eq27006 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq27006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27006
  have eq27311 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27310
  have eq27314 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27311
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27311
    | exact resolve eq27311 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27311
  have eq27694 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3395 x y
       have i₂ := eq27314
       grind)
    | exact superpose eq27314 eq3395
    | exact resolve eq3395 eq27314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq29823 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27314
       have i₂ := eq27694
       grind)
    | exact superpose eq27694 eq27314
    | exact resolve eq27314 eq27694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27314 eq27694
  have eq29865 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq29823
  have eq29898 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq29865
       grind)
    | exact superpose eq29865 eq52
    | exact resolve eq52 eq29865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29865
  have eq29919 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq29898
  have eq29983 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20538 y y
       have i₂ := eq29919
       grind)
    | exact superpose eq29919 eq20538
    | exact resolve eq20538 eq29919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20538 eq29919
  have eq29987 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29983
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29983
    | exact resolve eq29983 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29983
  have eq29988 : x = (M.op x y) := by grind
  clear eq29987
  have eq30003 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq29988 eq21
    | exact resolve eq21 eq29988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30075 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq29988 eq3421
    | exact resolve eq3421 eq29988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq30129 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30075
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30075
    | exact resolve eq30075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30075
  have eq30189 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30003
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30003
    | exact resolve eq30003 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30003
  have eq30192 : x = (M.op y y) := by
    first
    | exact superpose eq29988 eq30129
    | exact resolve eq30129 eq29988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30129
  have eq30194 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30189 eq27
    | exact resolve eq27 eq30189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30379 : x = (k x y) := by grind
  have eq30392 : y = (M.op x x) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq30192
       grind)
    | exact superpose eq30192 eq52
    | exact resolve eq52 eq30192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq30192
  have eq30663 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq30392
       grind)
    | exact superpose eq30392 eq80
    | exact resolve eq80 eq30392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq30392
  have eq30721 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq30189 eq30663
    | exact resolve eq30663 eq30189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30663
  have eq30729 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq30721
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30721
    | exact resolve eq30721 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30721
  have eq32789 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq30729 eq3775
    | (have j0 := eq3775 (σ (M.op x y))
       grind)
    | exact resolve eq3775 eq30729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq32805 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq30194 eq32789
    | exact resolve eq32789 eq30194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32789
  have eq32816 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq32805
       have r₂ := eq28
       grind)
    | exact resolve eq32805 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32805
  have eq32931 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq32816
  have eq33101 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32931 eq30729
    | exact resolve eq30729 eq32931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30729 eq32931
  have eq33124 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq33101
  have eq33162 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq33124 eq30
    | exact resolve eq30 eq33124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq33124
  have eq33380 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq33162
    | exact resolve eq33162 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33162
  have eq33441 : x = y ∨ x = y := by
    first
    | exact superpose eq29988 eq33380
    | exact resolve eq33380 eq29988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33380
  have eq33442 : x = y := by grind
  clear eq33441
  have eq33492 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq33442
       grind)
    | exact superpose eq33442 eq25
    | exact resolve eq25 eq33442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq33622 : x = (k x x) := by
    first
    | (have i₁ := eq30379
       have i₂ := eq33442
       grind)
    | exact superpose eq33442 eq30379
    | exact resolve eq30379 eq33442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30379 eq33442
  have eq33737 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq33492
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33492
    | exact resolve eq33492 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33492
  have eq33816 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30189 eq33737
    | exact resolve eq33737 eq30189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33737
  have eq34047 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33816 eq30194
    | exact resolve eq30194 eq33816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30194 eq33816
  have eq34439 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34047 eq208
    | exact resolve eq208 eq34047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq34047
  have eq34493 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq34439
       have r₂ := eq28
       grind)
    | exact resolve eq34439 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34439
  have eq34505 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29988 eq34493
    | exact resolve eq34493 eq29988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29988 eq34493
  have eq34509 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq34505
       have i₂ := eq33622
       grind)
    | exact superpose eq33622 eq34505
    | exact resolve eq34505 eq33622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33622 eq34505
  have eq34510 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34509 eq15
    | exact resolve eq15 eq34509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34509
  have eq34608 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34510
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34510
    | exact resolve eq34510 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq34510
  have eq34644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30189 eq34608
    | exact resolve eq34608 eq30189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30189 eq34608
  have eq34668 : False := by grind
  exact eq34668

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
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
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq103
    | exact resolve eq103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq234 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq28 eq57
    | (have j0 := eq57 (σ y) (σ x)
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq241 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq237 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq237
    | exact resolve eq237 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq362 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (k X0 X0))) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq14
    | (have j1 := eq69 X0
       grind)
    | exact resolve eq14 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq443 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq55
  have eq3293 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X0 X1
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq443
    | exact resolve eq443 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq443
  have eq3320 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq28 eq3293
    | (have j0 := eq3293 (σ y) (σ x)
       grind)
    | exact resolve eq3293 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6274 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq362 X0 x
       have i₂ := eq3293 (σ (k X0 X0)) x
       grind)
    | exact superpose eq3293 eq362
    | (have j0 := eq362 X0 x
       grind)
    | exact resolve eq362 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq12556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq12556
    | exact resolve eq12556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12556
  have eq12568 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12557
       have r₂ := eq29
       grind)
    | exact resolve eq12557 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12593 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq12568 eq3293
    | exact resolve eq3293 eq12568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12568
  have eq12594 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq12593
    | exact resolve eq12593 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12593
  have eq12606 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12594
  have eq12628 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12606
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq12606
    | exact resolve eq12606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12606
  have eq13071 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq12628
       grind)
    | exact superpose eq12628 eq46
    | exact resolve eq46 eq12628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq12628
  have eq13093 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq13071
    | exact resolve eq13071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13071
  have eq13519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13093 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13093
  have eq13520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13519
  have eq13522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq13520
    | exact resolve eq13520 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13520
  have eq13533 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13522
       have r₂ := eq29
       grind)
    | exact resolve eq13522 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13522
  have eq14234 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13533 eq3293
    | exact resolve eq3293 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533
  have eq14237 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq14234
    | exact resolve eq14234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14234
  have eq14238 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14237
  have eq14244 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14238 eq29
    | exact resolve eq29 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14252 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14238 eq3320
    | exact resolve eq3320 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq14265 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq14252
    | exact resolve eq14252 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14252
  have eq14269 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14265 eq234
    | exact resolve eq234 eq14265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq14265
  have eq14324 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14269 eq241
    | exact resolve eq241 eq14269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq14383 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14238 eq14324
    | exact resolve eq14324 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14238 eq14324
  have eq14393 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14383
  have eq14614 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14393 eq104
    | exact resolve eq104 eq14393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq14393
  have eq14628 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq14614
  have eq14639 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14628
       have r₂ := eq14244
       grind)
    | exact resolve eq14628 eq14244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14628
  have eq14738 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3293 y y
       have i₂ := eq14639
       grind)
    | exact superpose eq14639 eq3293
    | exact resolve eq3293 eq14639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq14639
  have eq14740 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14738
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14738
    | exact resolve eq14738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14738
  have eq14748 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14740 eq31
    | exact resolve eq31 eq14740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14740
  have eq14874 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14748
    | exact resolve eq14748 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14748
  have eq14875 : x = (M.op x y) ∨ x = y := by grind
  clear eq14874
  have eq14876 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14875 eq22
    | exact resolve eq22 eq14875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14993 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14876
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14876
    | exact resolve eq14876 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14876
  have eq15072 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14993 eq14244
    | (have r₁ := eq14244
       have r₂ := eq14993
       grind)
    | exact resolve eq14244 eq14993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14244 eq14993
  have eq15081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq15072
  have eq15082 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq15081
  have eq15155 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq15082 eq31
    | exact resolve eq31 eq15082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15082
  have eq15318 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq15155
    | exact resolve eq15155 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15155
  have eq15387 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15318 eq14875
    | exact resolve eq14875 eq15318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14875 eq15318
  have eq15388 : x = y := by grind
  clear eq15387
  have eq15440 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq15388
       grind)
    | exact superpose eq15388 eq20
    | exact resolve eq20 eq15388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq15441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq15388
       grind)
    | exact superpose eq15388 eq26
    | exact resolve eq26 eq15388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15388
  have eq15552 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15441
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15441
    | exact resolve eq15441 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15441
  have eq15555 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15552 eq28
    | exact resolve eq28 eq15552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15552
  have eq15688 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq15440
       grind)
    | exact superpose eq15440 eq71
    | exact resolve eq71 eq15440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq15700 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq241 x
       have i₂ := eq15440
       grind)
    | exact superpose eq15440 eq241
    | exact resolve eq241 eq15440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15440
  have eq15719 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq15688
    | exact resolve eq15688 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15688
  have eq15946 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15555 eq241
    | exact resolve eq241 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq17061 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq17074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15555 eq17061
    | exact resolve eq17061 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17061
  have eq17087 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17074
       have r₂ := eq29
       grind)
    | exact resolve eq17074 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17074
  have eq17093 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15555 eq17087
    | exact resolve eq17087 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17087
  have eq17098 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17093 eq29
    | exact resolve eq29 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17122 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17093 eq15946
    | exact resolve eq15946 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946 eq17093
  have eq17294 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17122 eq15719
    | exact resolve eq15719 eq17122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15719 eq17122
  have eq17311 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq17294
  have eq17321 : x = (M.op x y) := by
    first
    | (have r₁ := eq17311
       have r₂ := eq17098
       grind)
    | exact resolve eq17311 eq17098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17098 eq17311
  have eq17347 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17321 eq22
    | exact resolve eq22 eq17321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq17418 : x = (k x x) := by
    first
    | exact superpose eq17321 eq15700
    | exact resolve eq15700 eq17321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15700 eq17321
  have eq17484 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17347
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17347
    | exact resolve eq17347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17347
  have eq17812 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6274 x
       have i₂ := eq17418
       grind)
    | exact superpose eq17418 eq6274
    | (have j0 := eq6274 x
       grind)
    | exact resolve eq6274 eq17418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6274 eq17418
  have eq17813 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17812
  have eq17824 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17813
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17813
    | exact resolve eq17813 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17813
  have eq17842 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15555 eq17824
    | exact resolve eq17824 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15555 eq17824
  have eq17856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17484 eq17842
    | exact resolve eq17842 eq17484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484 eq17842
  have eq17870 : False := by grind
  exact eq17870

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq84
    | exact resolve eq84 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq84
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq123 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq499 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq123
    | exact resolve eq123 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq500 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq499
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq499
    | exact resolve eq499 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq517 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq500
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq500
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq500 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq500
  have eq518 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq517
  have eq3989 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq518
       grind)
    | exact superpose eq518 eq10
    | exact resolve eq10 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq4036 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3989
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq3989
    | exact resolve eq3989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq4037 : (M.op x x) = (M.op y y) := by grind
  clear eq4036
  have eq4086 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq75 y y
       have i₂ := eq4037
       grind)
    | exact superpose eq4037 eq75
    | exact resolve eq75 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037
  have eq4115 : x = y := by
    first
    | (have i₁ := eq4086
       have i₂ := eq75 x x
       grind)
    | exact superpose eq75 eq4086
    | exact resolve eq4086 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq4086
  have eq4180 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4115
       grind)
    | exact superpose eq4115 eq16
    | exact resolve eq16 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq4181 : False := by grind
  exact eq4181

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq72
    | exact resolve eq72 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq230 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (k (M.op X1 (M.op X0 X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (k (M.op X1 (M.op X0 X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230 X0 X1 X2
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq230
    | (have j0 := eq230 X0 X1 X2
       grind)
    | (have r₁ := eq230 X0 (M.op X1 X0) X0
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq230 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq243 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq243
    | (have j0 := eq243 (σ X0) (σ X1)
       grind)
    | exact resolve eq243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq243 X1 (τ X0)
       grind)
    | exact superpose eq243 eq18
    | (have j1 := eq243 X1 (τ X0)
       grind)
    | exact resolve eq18 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq418 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq545 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq418
    | exact resolve eq418 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq584 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq545
    | exact resolve eq545 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq1013 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq244 y x
       grind)
    | exact superpose eq244 eq16
    | (have j1 := eq244 y x
       grind)
    | exact resolve eq16 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ (k X0 X1))) (M.op (σ X1) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq244 X0 X1
       grind)
    | exact superpose eq244 eq9
    | (have j1 := eq244 X0 X1
       grind)
    | exact resolve eq9 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq4688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq242 X0 X1 X2
       have i₂ := eq584 (M.op X0 X2) X1
       grind)
    | exact superpose eq584 eq242
    | (have j0 := eq242 X0 X1 X2
       grind)
    | exact resolve eq242 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq584
  have eq5364 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq253
    | exact resolve eq253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq5401 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5364 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5364
    | (have j0 := eq5364 X0 X1
       grind)
    | exact resolve eq5364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5364
  have eq6293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq243 y x
       grind)
    | exact superpose eq243 eq1013
    | (have j1 := eq243 (σ y) (σ x)
       grind)
    | exact resolve eq1013 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq6296 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6293
  have eq6306 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88 (σ x) (σ y)
       have i₂ := eq6296
       grind)
    | exact superpose eq6296 eq88
    | exact resolve eq88 eq6296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6602 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6296
       have i₂ := eq6306
       grind)
    | exact superpose eq6306 eq6296
    | exact resolve eq6296 eq6306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6296 eq6306
  have eq6658 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6602
  have eq6673 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62 (σ x)
       have i₂ := eq6658
       grind)
    | exact superpose eq6658 eq62
    | exact resolve eq62 eq6658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6759 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6673
       grind)
    | exact superpose eq6673 eq16
    | exact resolve eq16 eq6673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq8247 : ∀ X0 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq4688 (σ x) (M.op X2 (σ (k X0 x))) (σ x)
       have i₂ := eq1014 X0 x X2
       grind)
    | exact superpose eq1014 eq4688
    | (have j0 := eq4688 (σ X0) x X2
       have j1 := eq1014 X0 X0 X2
       grind)
    | (have r₁ := eq4688 (σ x) (M.op X2 (σ (k X0 x))) (σ x)
       have r₂ := eq1014 X0 x X2
       grind)
    | exact resolve eq4688 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq4688
  have eq8303 : ∀ X0 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq8247 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247
  have eq8304 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq8303 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8303
  have eq8335 : ∀ X0 : G, (k (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq8304 X0
       have j1 := eq85 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq8304 X0
       have r₂ := eq85 (σ X0) x
       grind)
    | exact resolve eq8304 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq8304
  have eq8354 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8335 X0
       have i₂ := eq88 (σ X0) (σ X0)
       grind)
    | exact superpose eq88 eq8335
    | exact resolve eq8335 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335
  have eq8372 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8354 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8354
    | exact resolve eq8354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8354
  have eq8395 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8372 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq8372
    | exact resolve eq8372 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq8372
  have eq8441 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8395 (σ x)
       have i₂ := eq6658
       grind)
    | exact superpose eq6658 eq8395
    | exact resolve eq8395 eq6658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6658
  have eq8461 : (σ x) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8441
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8441
    | exact resolve eq8441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441
  have eq9059 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5401 x y
       have i₂ := eq8461
       grind)
    | exact superpose eq8461 eq5401
    | (have j0 := eq5401 x y
       grind)
    | exact resolve eq5401 eq8461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401 eq8461
  have eq9081 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq9059
  have eq9097 : y = (M.op y x) := by
    first
    | (have r₁ := eq9081
       have r₂ := eq6759
       grind)
    | exact resolve eq9081 eq6759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6759 eq9081
  have eq9107 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq9097
       grind)
    | exact superpose eq9097 eq88
    | exact resolve eq88 eq9097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9164 : y = (M.op x x) := by
    first
    | (have i₁ := eq9107
       have i₂ := eq9097
       grind)
    | exact superpose eq9097 eq9107
    | exact resolve eq9107 eq9097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9097 eq9107
  have eq9169 : x = (M.op x y) := by
    first
    | (have i₁ := eq62 x
       have i₂ := eq9164
       grind)
    | exact superpose eq9164 eq62
    | exact resolve eq62 eq9164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9187 : x = (k y x) := by
    first
    | (have i₁ := eq8395 x
       have i₂ := eq9164
       grind)
    | exact superpose eq9164 eq8395
    | exact resolve eq8395 eq9164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8395 eq9164
  have eq9353 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq9187
       grind)
    | exact superpose eq9187 eq1013
    | exact resolve eq1013 eq9187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq9187
  have eq9358 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9353
       have i₂ := eq9169
       grind)
    | exact superpose eq9169 eq9353
    | exact resolve eq9353 eq9169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9353
  have eq9359 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq9358
  have eq10779 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq88 (σ x) (σ y)
       have i₂ := eq9359
       grind)
    | exact superpose eq9359 eq88
    | exact resolve eq88 eq9359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq10839 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10779
       have i₂ := eq9359
       grind)
    | exact superpose eq9359 eq10779
    | exact resolve eq10779 eq9359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9359 eq10779
  have eq10857 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62 (σ x)
       have i₂ := eq10839
       grind)
    | exact superpose eq10839 eq62
    | exact resolve eq62 eq10839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq10839
  have eq10955 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10857
       grind)
    | exact superpose eq10857 eq16
    | exact resolve eq16 eq10857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857
  have eq11044 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq10955
       have i₂ := eq9169
       grind)
    | exact superpose eq9169 eq10955
    | exact resolve eq10955 eq9169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9169 eq10955
  have eq11045 : False := by grind
  exact eq11045
