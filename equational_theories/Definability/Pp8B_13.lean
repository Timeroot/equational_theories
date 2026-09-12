import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyy_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq51 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq103
  have eq111 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq171 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq193 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq210 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq51 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq57 X0 X0
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq57 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq53 y X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq511 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq53 sF3 x x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq612 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq621 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq718 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq229 sF4
       have i₂ := eq57 sF4 sF3
       grind)
    | exact superpose eq57 eq229
    | exact resolve eq229 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq779 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq94 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq791 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq779 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq779 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq779 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq779 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq801 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq791 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq791
    | (have j0 := eq791 X0 X1
       grind)
    | exact resolve eq791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq1134 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq241 X0 x x
       grind)
    | exact superpose eq241 eq57
    | exact resolve eq57 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1134 X0
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq1134
    | exact resolve eq1134 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq3320 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq612 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1137 sF4
       grind)
    | exact superpose eq1137 eq612
    | exact resolve eq612 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3343 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3320
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3320
    | exact resolve eq3320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3360 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3343 eq612
    | exact resolve eq612 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3585 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq718 eq219
    | exact resolve eq219 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq718
  have eq3614 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3585 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3585
    | exact resolve eq3585 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585
  have eq3615 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3614 x
       have i₂ := eq57 sF4 x
       grind)
    | exact superpose eq57 eq3614
    | exact resolve eq3614 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614
  have eq3616 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3343 eq3615
    | exact resolve eq3615 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343 eq3615
  have eq3617 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3616 eq3360
    | exact resolve eq3360 eq3616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq4021 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq240 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4728 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq502 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq241 X0 x X2
       grind)
    | exact superpose eq241 eq502
    | exact resolve eq502 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq4820 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq4728 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq4728
    | exact resolve eq4728 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728
  have eq4830 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq4820 X0 x
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq4820
    | exact resolve eq4820 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820
  have eq5595 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq171 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq171
    | (have j0 := eq171 x
       grind)
    | exact resolve eq171 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq5612 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5595
  have eq5616 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5612
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5612
    | exact resolve eq5612 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5612
  have eq5633 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5616
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5616 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5616
  have eq5642 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5633 eq50
    | exact resolve eq50 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5848 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq193 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq193
    | (have j0 := eq193 y
       grind)
    | exact resolve eq193 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq5866 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5848
  have eq5869 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5866
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq5866
    | exact resolve eq5866 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq5866
  have eq5893 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5869
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5869 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5869
  have eq5921 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5893 eq88
    | exact resolve eq88 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq6582 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq621 X0 X1 X2 X3
       have i₂ := eq4830 X0
       grind)
    | exact superpose eq4830 eq621
    | exact resolve eq621 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq6650 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6582 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq241 X0 x x
       grind)
    | exact superpose eq241 eq6582
    | exact resolve eq6582 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6864 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6650 X0 X1 X2
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq6650
    | exact resolve eq6650 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6650
  have eq6899 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6864 X0 X1 X2
       have i₂ := eq4830 X0
       grind)
    | exact superpose eq4830 eq6864
    | exact resolve eq6864 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830 eq6864
  have eq6968 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq6899
    | (have j0 := eq6899 (σ y) X0 (σ x)
       grind)
    | exact resolve eq6899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7047 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq6899 X0 X0 sF4
       grind)
    | exact superpose eq6899 eq612
    | exact resolve eq612 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq8885 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq6899 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq6899 eq510
    | exact resolve eq510 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq8914 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y x X0
       have i₂ := eq8885 X0 x
       grind)
    | exact superpose eq8885 eq53
    | exact resolve eq53 eq8885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8885
  have eq9050 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8914 (M.op X0 (M.op X0 X0))
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq8914
    | exact resolve eq8914 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8914
  have eq9168 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1137 X0
       have i₂ := eq9050 X0
       grind)
    | exact superpose eq9050 eq1137
    | exact resolve eq1137 eq9050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9188 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7047 sF4
       have i₂ := eq9050 sF4
       grind)
    | exact superpose eq9050 eq7047
    | exact resolve eq7047 eq9050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7047 eq9050
  have eq9311 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3616 eq9188
    | exact resolve eq9188 eq3616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616 eq9188
  have eq9385 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq6899 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq6899 eq511
    | exact resolve eq511 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq6899
  have eq9647 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9385 eq53
    | exact resolve eq53 eq9385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9385
  have eq9797 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9647 (M.op X0 (M.op X0 X0))
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq9647
    | exact resolve eq9647 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq9647
  have eq10197 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9797 eq14
    | exact resolve eq14 eq9797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9797
  have eq10220 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10197 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq10197
    | exact resolve eq10197 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10197
  have eq10847 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10220 eq620
    | exact resolve eq620 eq10220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq10220
  have eq10848 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3617 eq10847
    | exact resolve eq10847 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617 eq10847
  have eq10849 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6968 eq10848
    | exact resolve eq10848 eq6968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968 eq10848
  have eq10878 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq10849 (M.op x (M.op x x)) x sF2
       have i₂ := eq53 x x sF2
       grind)
    | exact superpose eq53 eq10849
    | exact resolve eq10849 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq10849
  have eq13914 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9311 eq10878
    | exact resolve eq10878 eq9311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9311 eq10878
  have eq36003 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5893 eq110
    | exact resolve eq110 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq5893
  have eq36758 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5633 eq111
    | exact resolve eq111 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq5633
  have eq36769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq36779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq36769
    | exact resolve eq36769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36769
  have eq36790 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq36779
       have r₂ := eq28
       grind)
    | exact resolve eq36779 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36779
  have eq36792 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq36790
    | exact resolve eq36790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36790
  have eq36796 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq36792 eq5642
    | exact resolve eq5642 eq36792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642 eq36792
  have eq36920 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq36796
    | exact resolve eq36796 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36796
  have eq41163 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq36920
       grind)
    | exact superpose eq36920 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq36920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41181 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41163
  have eq42583 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq240 x x
       have i₂ := eq41181
       grind)
    | exact superpose eq41181 eq240
    | exact resolve eq240 eq41181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42613 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq42614 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42583
  have eq42637 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42614
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42614
    | exact resolve eq42614 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42614
  have eq43689 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq42637
       grind)
    | exact superpose eq42637 eq45
    | exact resolve eq45 eq42637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq42637
  have eq43723 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq43689
    | exact resolve eq43689 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43689
  have eq65674 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36758
       have i₂ := eq41181
       grind)
    | exact superpose eq41181 eq36758
    | exact resolve eq36758 eq41181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36758 eq41181
  have eq65754 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq65674
       have r₂ := eq42613
       grind)
    | exact resolve eq65674 eq42613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42613 eq65674
  have eq65766 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65754
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65754
    | exact resolve eq65754 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65754
  have eq65920 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65766 eq240
    | exact resolve eq240 eq65766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq65766
  have eq65953 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq65920
  have eq65982 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq65953
    | exact resolve eq65953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65953
  have eq173172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65982 eq43723
    | exact resolve eq43723 eq65982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43723 eq65982
  have eq173187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq173172
  have eq173195 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq173187
       have r₂ := eq28
       grind)
    | exact resolve eq173187 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173187
  have eq173224 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1137 x
       have i₂ := eq173195
       grind)
    | exact superpose eq173195 eq1137
    | exact resolve eq1137 eq173195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq173225 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4021 x
       have i₂ := eq173195
       grind)
    | exact superpose eq173195 eq4021
    | exact resolve eq4021 eq173195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021 eq173195
  have eq179416 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36920
       have i₂ := eq173225
       grind)
    | exact superpose eq173225 eq36920
    | exact resolve eq36920 eq173225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36920 eq173225
  have eq179451 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq179416
  have eq179503 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173224
       have i₂ := eq179451
       grind)
    | exact superpose eq179451 eq173224
    | exact resolve eq173224 eq179451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173224 eq179451
  have eq179652 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq179503
  have eq179751 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq179652
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq179652
    | exact resolve eq179652 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179652
  have eq179752 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq179751
  have eq180231 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179752 eq13914
    | exact resolve eq13914 eq179752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13914 eq179752
  have eq180684 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9168 eq180231
    | exact resolve eq180231 eq9168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9168 eq180231
  have eq180743 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq180684 eq5921
    | exact resolve eq5921 eq180684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180684
  have eq181040 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq180743
    | exact resolve eq180743 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq180743
  have eq181805 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq181040
       grind)
    | exact superpose eq181040 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq181040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181823 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq181805
  have eq365571 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq181823
       grind)
    | exact superpose eq181823 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq181823
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq181823
       grind)
    | exact resolve eq13 eq181823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365641 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq181823
  have eq365647 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq365571
  have eq376081 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181040
       have i₂ := eq365647
       grind)
    | exact superpose eq365647 eq181040
    | exact resolve eq181040 eq365647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181040 eq365647
  have eq376143 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq376081
  have eq376184 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq376143
       have r₂ := eq365641
       grind)
    | exact resolve eq376143 eq365641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365641 eq376143
  have eq376379 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq376184
       grind)
    | exact superpose eq376184 eq57
    | exact resolve eq57 eq376184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376184
  have eq376499 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq376379
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq376379
    | exact resolve eq376379 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376379
  have eq376500 : x = (M.op x y) := by grind
  clear eq376499
  have eq376551 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq376500 eq21
    | exact resolve eq21 eq376500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq376601 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq376500 eq210
    | exact resolve eq210 eq376500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq376916 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq376601
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq376601
    | exact resolve eq376601 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq376601
  have eq376961 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq376551
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq376551
    | exact resolve eq376551 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376551
  have eq376969 : x = (M.op y y) := by
    first
    | exact superpose eq376500 eq376916
    | exact resolve eq376916 eq376500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376916
  have eq377034 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq376961 eq27
    | exact resolve eq27 eq376961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq377799 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36003
       have i₂ := eq376969
       grind)
    | exact superpose eq376969 eq36003
    | exact resolve eq36003 eq376969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36003
  have eq377926 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq376969
       grind)
    | exact superpose eq376969 eq13
    | exact resolve eq13 eq376969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376969
  have eq378091 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq377799
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq377799
    | exact resolve eq377799 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377799
  have eq378141 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq376961 eq378091
    | exact resolve eq378091 eq376961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378091
  have eq381295 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq378141 eq5921
    | exact resolve eq5921 eq378141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5921
  have eq381499 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq378141 eq57
    | exact resolve eq57 eq378141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq378141
  have eq381599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq377034 eq381499
    | exact resolve eq381499 eq377034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381499
  have eq381663 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq381295
    | exact resolve eq381295 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq381295
  have eq381678 : x = y := by
    first
    | (have r₁ := eq381599
       have r₂ := eq28
       grind)
    | exact resolve eq381599 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381599
  have eq381699 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq376500 eq381663
    | exact resolve eq381663 eq376500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376500 eq381663
  have eq381715 : x = (k y y) := by
    first
    | (have r₁ := eq381699
       have r₂ := eq377926
       grind)
    | exact resolve eq381699 eq377926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377926 eq381699
  have eq381724 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq381678
       grind)
    | exact superpose eq381678 eq25
    | exact resolve eq25 eq381678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq382533 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq381724
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq381724
    | exact resolve eq381724 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381724
  have eq382701 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq376961 eq382533
    | exact resolve eq382533 eq376961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382533
  have eq384702 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq382701 eq377034
    | exact resolve eq377034 eq382701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377034 eq382701
  have eq385057 : x = (k x x) := by
    first
    | (have i₁ := eq381715
       have i₂ := eq381678
       grind)
    | exact superpose eq381678 eq381715
    | exact resolve eq381715 eq381678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381678 eq381715
  have eq385097 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq801 x x
       have i₂ := eq385057
       grind)
    | exact superpose eq385057 eq801
    | (have j0 := eq801 x x
       grind)
    | exact resolve eq801 eq385057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq385057
  have eq385102 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq385097
  have eq385103 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq385102
  have eq385119 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq385103
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq385103
    | exact resolve eq385103 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq385103
  have eq385146 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq376961 eq385119
    | exact resolve eq385119 eq376961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376961 eq385119
  have eq389587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385146 eq384702
    | exact resolve eq384702 eq385146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384702 eq385146
  have eq389588 : False := by grind
  exact eq389588

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyy_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq210 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq47 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op X1 x)) (M.op (M.op y (M.op x y)) y)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq53 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq49 y X1 X0
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq49 sF3 x x
       grind)
    | exact superpose eq49 eq48
    | exact resolve eq48 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq766 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X0)) X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op (M.op X0 (M.op y X0)) X0) (M.op X0 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq52
    | exact resolve eq52 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X0 (M.op X1 X2)))) = (M.op (M.op X3 (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X0 (M.op X1 X2)))))) (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X0 (M.op X1 X2)))) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X2 X3)) X1 X2 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 (M.op X1 (M.op X2 X3))))
       have i₂ := eq52 (M.op X1 (M.op X2 X3)) X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq53 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op x (M.op x X1))
       have i₂ := eq52 X0 x x X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq822 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq229 sF4
       have i₂ := eq53 sF4 sF3
       grind)
    | exact superpose eq53 eq229
    | exact resolve eq229 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq872 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq66 X0 X0
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq882 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq885 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq882 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq882 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq882 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq882 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq896 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1305 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq241 X0 x x
       grind)
    | exact superpose eq241 eq53
    | exact resolve eq53 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1305 X0
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq1305
    | exact resolve eq1305 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq3542 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq766 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1308 sF0
       grind)
    | exact superpose eq1308 eq766
    | exact resolve eq766 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3565 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3542
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3542
    | exact resolve eq3542 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542
  have eq3567 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3565 eq766
    | exact resolve eq766 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq3565
  have eq3588 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3567 eq14
    | exact resolve eq14 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3615 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq767 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1308 sF4
       grind)
    | exact superpose eq1308 eq767
    | exact resolve eq767 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3638 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3615
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3615
    | exact resolve eq3615 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615
  have eq3655 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3638 eq767
    | exact resolve eq767 eq3638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3729 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3588 eq47
    | exact resolve eq47 eq3588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3750 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq3729 eq3567
    | exact resolve eq3567 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq3882 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq822 eq219
    | exact resolve eq219 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq822
  have eq3911 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3882 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3882
    | exact resolve eq3882 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq3912 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3911 x
       have i₂ := eq53 sF4 x
       grind)
    | exact superpose eq53 eq3911
    | exact resolve eq3911 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911
  have eq3913 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3638 eq3912
    | exact resolve eq3912 eq3638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638 eq3912
  have eq3914 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3913 eq3655
    | exact resolve eq3655 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655
  have eq5123 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq444 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq241 X0 x X2
       grind)
    | exact superpose eq241 eq444
    | exact resolve eq444 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5216 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5123 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5123
    | exact resolve eq5123 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123
  have eq5227 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5216 X0 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq5216
    | exact resolve eq5216 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq6952 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq776 X0 X1 X2 X3
       have i₂ := eq5227 X0
       grind)
    | exact superpose eq5227 eq776
    | exact resolve eq776 eq5227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq7052 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6952 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq241 X0 x x
       grind)
    | exact superpose eq241 eq6952
    | exact resolve eq6952 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6952
  have eq7265 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7052 X0 X1 X2
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq7052
    | exact resolve eq7052 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052
  have eq7300 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7265 X0 X1 X2
       have i₂ := eq5227 X0
       grind)
    | exact superpose eq5227 eq7265
    | exact resolve eq7265 eq5227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227 eq7265
  have eq7356 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7300 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7300
    | (have j0 := eq7300 y X0 x
       grind)
    | exact resolve eq7300 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7369 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq7300
    | (have j0 := eq7300 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7448 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq767 X0
       have i₂ := eq7300 X0 X0 sF4
       grind)
    | exact superpose eq7300 eq767
    | exact resolve eq767 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq7584 : (M.op y (M.op y y)) = (M.op (M.op x y) (M.op (M.op y (M.op y y)) y)) := by
    first
    | exact superpose eq7356 eq444
    | exact resolve eq444 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7610 : (M.op y (M.op y y)) = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq7584
       have i₂ := eq7300 y y y
       grind)
    | exact superpose eq7300 eq7584
    | exact resolve eq7584 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584
  have eq7619 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) := by
    first
    | exact superpose eq7369 eq444
    | exact resolve eq444 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq7645 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7619
       have i₂ := eq7300 sF3 sF3 sF3
       grind)
    | exact superpose eq7300 eq7619
    | exact resolve eq7619 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7619
  have eq7646 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq785 X0
       have i₂ := eq7300 X0 X0 X0
       grind)
    | exact superpose eq7300 eq785
    | exact resolve eq785 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq8942 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq7300 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7300 eq452
    | exact resolve eq452 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq8971 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y x X0
       have i₂ := eq8942 X0 x
       grind)
    | exact superpose eq8942 eq49
    | exact resolve eq49 eq8942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8942
  have eq9102 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8971 (M.op X0 (M.op X0 X0))
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq8971
    | exact resolve eq8971 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9220 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1308 X0
       have i₂ := eq9102 X0
       grind)
    | exact superpose eq9102 eq1308
    | exact resolve eq1308 eq9102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9226 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq9102 X0
       grind)
    | exact superpose eq9102 eq14
    | exact resolve eq14 eq9102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9240 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7448 sF4
       have i₂ := eq9102 sF4
       grind)
    | exact superpose eq9102 eq7448
    | exact resolve eq7448 eq9102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448
  have eq9304 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9102 eq14
    | exact resolve eq14 eq9102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9328 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9304 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq9304
    | exact resolve eq9304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9304
  have eq9362 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3913 eq9240
    | exact resolve eq9240 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913 eq9240
  have eq9437 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq7300 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7300 eq453
    | exact resolve eq453 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq9702 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9437 eq49
    | exact resolve eq49 eq9437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9437
  have eq9847 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9702 (M.op X0 (M.op X0 X0))
       have i₂ := eq241 X0 X0 X0
       grind)
    | exact superpose eq241 eq9702
    | exact resolve eq9702 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq10232 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9847 eq14
    | exact resolve eq14 eq9847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10256 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10232 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq10232
    | exact resolve eq10232 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10232
  have eq10875 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10256 eq775
    | exact resolve eq775 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq10876 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3914 eq10875
    | exact resolve eq10875 eq3914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq10877 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7369 eq10876
    | exact resolve eq10876 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10876
  have eq10906 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq10877 (M.op x (M.op x x)) x sF2
       have i₂ := eq49 x x sF2
       grind)
    | exact superpose eq49 eq10877
    | exact resolve eq10877 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq10877
  have eq12540 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9362 eq10906
    | exact resolve eq10906 eq9362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906
  have eq16173 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op X0 X0) (M.op X0 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq778 X0 X1 X2
       have i₂ := eq7300 X0 X0 y
       grind)
    | exact superpose eq7300 eq778
    | exact resolve eq778 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq16237 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op x y)) (M.op y (M.op y (M.op x y)))))) := by
    intro X0 X1
    first
    | exact superpose eq231 eq16173
    | exact resolve eq16173 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16173
  have eq16382 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3588 eq16237
    | exact resolve eq16237 eq3588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16237
  have eq16424 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16382 X0 X1
       have i₂ := eq7300 sF0 y y
       grind)
    | exact superpose eq7300 eq16382
    | exact resolve eq16382 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16382
  have eq16451 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3729 eq16424
    | exact resolve eq16424 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16424
  have eq17715 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq240 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq17735 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17715 X0
       have i₂ := eq7646 X0
       grind)
    | exact superpose eq7646 eq17715
    | (have j0 := eq17715 X0
       grind)
    | exact resolve eq17715 eq7646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17715
  have eq17787 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq17735 X0
       have i₂ := eq7646 X0
       grind)
    | exact superpose eq7646 eq17735
    | (have j0 := eq17735 X0
       grind)
    | exact resolve eq17735 eq7646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735
  have eq19078 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 x
       have i₂ := eq7300 X0 X0 x
       grind)
    | exact superpose eq7300 eq796
    | exact resolve eq796 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq19079 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19078 X0 X1
       have i₂ := eq7646 X0
       grind)
    | exact superpose eq7646 eq19078
    | exact resolve eq19078 eq7646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7646 eq19078
  have eq19118 : (M.op (M.op (M.op y (M.op x y)) y) (M.op (M.op (M.op y (M.op x y)) y) (M.op (M.op y (M.op x y)) y))) = (M.op (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y))) (M.op (M.op (M.op y (M.op x y)) y) (M.op (M.op y (M.op x y)) y))) := by
    first
    | exact superpose eq225 eq19079
    | exact resolve eq19079 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19120 : (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)))) = (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)))) := by
    first
    | exact superpose eq228 eq19079
    | exact resolve eq19079 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19079
  have eq19424 : (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)))) = (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)))) := by
    first
    | exact superpose eq10256 eq19120
    | exact resolve eq19120 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19120
  have eq19426 : (M.op (M.op (M.op y (M.op x y)) y) (M.op (M.op x y) (M.op (M.op y (M.op x y)) y))) = (M.op (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y))) (M.op (M.op x y) (M.op (M.op y (M.op x y)) y))) := by
    first
    | (have i₁ := eq19118
       have i₂ := eq9328 (M.op (M.op y sF0) y) (M.op y sF0)
       grind)
    | exact superpose eq9328 eq19118
    | exact resolve eq19118 eq9328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19118
  have eq19524 : (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq7369 eq19424
    | exact resolve eq19424 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7369 eq19424
  have eq19526 : (M.op (M.op y y) (M.op (M.op x y) (M.op y y))) = (M.op (M.op (M.op y y) (M.op y (M.op x y))) (M.op (M.op x y) (M.op y y))) := by
    first
    | exact superpose eq7356 eq19426
    | exact resolve eq19426 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356 eq19426
  have eq19578 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq7645 eq19524
    | exact resolve eq19524 eq7645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7645 eq19524
  have eq19579 : (M.op (M.op y y) (M.op y (M.op y y))) = (M.op (M.op (M.op y y) (M.op y (M.op x y))) (M.op y (M.op y y))) := by
    first
    | exact superpose eq7610 eq19526
    | exact resolve eq19526 eq7610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7610 eq19526
  have eq19603 : (M.op (M.op (σ y) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq19578
       have i₂ := eq9102 sF3
       grind)
    | exact superpose eq9102 eq19578
    | exact resolve eq19578 eq9102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9102 eq19578
  have eq19604 : (M.op (M.op y y) (M.op y (M.op y y))) = (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq19579
       have i₂ := eq9328 (M.op y sF0) y
       grind)
    | exact superpose eq9328 eq19579
    | exact resolve eq19579 eq9328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9328 eq19579
  have eq19609 : (M.op (M.op (σ y) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | exact superpose eq10256 eq19603
    | exact resolve eq19603 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10256 eq19603
  have eq19610 : (M.op (M.op y y) (M.op y (M.op y y))) = (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y y))) := by
    first
    | exact superpose eq3750 eq19604
    | exact resolve eq19604 eq3750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750 eq19604
  have eq19611 : (M.op (M.op (σ y) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | exact superpose eq3914 eq19609
    | exact resolve eq19609 eq3914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3914 eq19609
  have eq19612 : y = (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq19610
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq19610
    | exact resolve eq19610 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19610
  have eq19613 : (M.op (M.op (σ y) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | exact superpose eq9362 eq19611
    | exact resolve eq19611 eq9362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19611
  have eq19614 : (σ y) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | exact superpose eq9226 eq19613
    | exact resolve eq19613 eq9226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19613
  have eq23148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq23149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23148
    | exact resolve eq23148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23148
  have eq23160 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23149
       have r₂ := eq28
       grind)
    | exact resolve eq23149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23149
  have eq23162 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23160
    | exact resolve eq23160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23160
  have eq23168 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq23162
  have eq23264 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23168 eq98
    | exact resolve eq98 eq23168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq23168
  have eq23290 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq23264
    | exact resolve eq23264 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23264
  have eq31621 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq23290
  have eq31679 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31621
  have eq31735 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq31679
       grind)
    | exact superpose eq31679 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq31679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31740 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq879 x y
       have i₂ := eq31679
       grind)
    | exact superpose eq31679 eq879
    | (have j0 := eq879 x y
       grind)
    | exact resolve eq879 eq31679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq31679
  have eq31744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31740
  have eq31745 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31735
  have eq31749 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31744
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31744
    | exact resolve eq31744 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31744
  have eq31754 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31745
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31745
    | exact resolve eq31745 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31745
  have eq31755 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31754
  have eq31767 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31749
    | exact resolve eq31749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31749
  have eq31774 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq31767
    | exact resolve eq31767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31767
  have eq31775 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq31774
  have eq31781 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31775
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31775
    | exact resolve eq31775 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31775
  have eq31788 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31781
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31781
    | exact resolve eq31781 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31781
  have eq32103 : y = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq31755
       grind)
    | exact superpose eq31755 eq50
    | exact resolve eq50 eq31755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32116 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9702 x
       have i₂ := eq31755
       grind)
    | exact superpose eq31755 eq9702
    | exact resolve eq9702 eq31755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9702 eq31755
  have eq32187 : x = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9847 eq32116
    | exact resolve eq32116 eq9847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847 eq32116
  have eq32251 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31788 eq51
    | exact resolve eq51 eq31788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq32262 : (σ x) = (M.op y (M.op (M.op x y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31788 eq8971
    | exact resolve eq8971 eq31788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8971 eq31788
  have eq32343 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9362 eq32251
    | exact resolve eq32251 eq9362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32251
  have eq35224 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X0 (M.op X1 X2)))) = (M.op (M.op X3 (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X0 (M.op X1 X2)))))) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq784 X0 X1 X2 X3 X4
       have i₂ := eq7300 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)) X2
       grind)
    | exact superpose eq7300 eq784
    | exact resolve eq784 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq7300
  have eq35857 : ∀ X2 X3 : G, (M.op (M.op y (M.op x y)) (M.op y (M.op y (M.op x y)))) = (M.op (M.op X2 (M.op X3 (M.op (M.op y (M.op x y)) (M.op y (M.op y (M.op x y)))))) (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq225 eq35224
    | (have j0 := eq35224 y x y X2 X3
       grind)
    | exact resolve eq35224 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq35859 : ∀ X2 X3 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op X2 (M.op X3 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq228 eq35224
    | (have j0 := eq35224 (σ y) (σ x) (σ y) X2 X3
       grind)
    | exact resolve eq35224 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq35224
  have eq36071 : ∀ X2 X3 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op X2 (M.op X3 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq232 eq35859
    | exact resolve eq35859 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq35859
  have eq36073 : ∀ X2 X3 : G, (M.op (M.op y (M.op x y)) (M.op y (M.op y (M.op x y)))) = (M.op (M.op X2 (M.op X3 (M.op (M.op y (M.op x y)) (M.op y (M.op y (M.op x y)))))) (M.op y (M.op y (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq231 eq35857
    | exact resolve eq35857 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq35857
  have eq36256 : ∀ X2 X3 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) = (M.op (M.op X2 (M.op X3 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq9362 eq36071
    | exact resolve eq36071 eq9362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9362 eq36071
  have eq36258 : ∀ X2 X3 : G, (M.op x y) = (M.op (M.op X2 (M.op X3 (M.op x y))) (M.op y (M.op y (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq3588 eq36073
    | exact resolve eq36073 eq3588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3588 eq36073
  have eq36366 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X3 (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq9226 eq36256
    | exact resolve eq36256 eq9226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9226 eq36256
  have eq68455 : y = (M.op (M.op y (M.op y (M.op x y))) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19612
       have i₂ := eq32187
       grind)
    | exact superpose eq32187 eq19612
    | exact resolve eq19612 eq32187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19612 eq32187
  have eq69540 : (σ y) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32262 eq19614
    | exact resolve eq19614 eq32262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19614 eq32262
  have eq82293 : y ≠ (M.op y (M.op y (M.op x y))) ∨ x = (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y (M.op x y)))) ∨ (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y (M.op x y)))) = (k x (M.op y (M.op y (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68455 eq12
    | (have j0 := eq12 x (M.op y (M.op y (M.op x y)))
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq68455
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq68455
       grind)
    | exact resolve eq12 eq68455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68455
  have eq82390 : x = (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y (M.op x y)))) ∨ (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y (M.op x y)))) = (k x (M.op y (M.op y (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq82293
       have r₂ := eq32103
       grind)
    | exact resolve eq82293 eq32103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82293
  have eq82413 : x = (M.op x y) ∨ (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y (M.op x y)))) = (k x (M.op y (M.op y (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36258 eq82390
    | exact resolve eq82390 eq36258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82390
  have eq82414 : x = (M.op x y) ∨ (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op y (M.op x y)))) = (k x (M.op y (M.op y (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82413
  have eq82420 : (M.op x y) = (k x (M.op y (M.op y (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36258 eq82414
    | exact resolve eq82414 eq36258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36258 eq82414
  have eq82440 : (σ y) ≠ (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) = (k (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69540 eq12
    | (have j0 := eq12 (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq69540
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq69540
       grind)
    | exact resolve eq12 eq69540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69540
  have eq82535 : (σ x) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) = (k (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq82440
       have r₂ := eq32343
       grind)
    | exact resolve eq82440 eq32343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82440
  have eq82560 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) = (k (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36366 eq82535
    | exact resolve eq82535 eq36366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82535
  have eq82561 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) = (k (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by grind
  clear eq82560
  have eq82569 : (M.op (σ x) (σ y)) = (k (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36366 eq82561
    | exact resolve eq82561 eq36366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36366 eq82561
  have eq126456 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32103 eq82420
    | exact resolve eq82420 eq32103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32103 eq82420
  have eq126468 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq126456
  have eq126518 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq126468
       grind)
    | exact superpose eq126468 eq45
    | exact resolve eq45 eq126468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq126468
  have eq126554 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq126518
    | exact resolve eq126518 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126518
  have eq126806 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32343 eq82569
    | exact resolve eq82569 eq32343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32343 eq82569
  have eq126819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq126806
  have eq126842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126819 eq126554
    | exact resolve eq126554 eq126819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126554 eq126819
  have eq126854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq126842
  have eq126857 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126854
       have r₂ := eq28
       grind)
    | exact resolve eq126854 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126854
  have eq126914 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126857 eq12540
    | exact resolve eq12540 eq126857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12540 eq126857
  have eq126949 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9220 eq126914
    | exact resolve eq126914 eq9220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9220 eq126914
  have eq127016 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq126949
  have eq127465 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127016 eq61
    | exact resolve eq61 eq127016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq127016
  have eq127503 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq127465
    | exact resolve eq127465 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq127465
  have eq127537 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq127503
       grind)
    | exact superpose eq127503 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq127503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127549 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq127537
  have eq210476 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq127549
       grind)
    | exact superpose eq127549 eq47
    | exact resolve eq47 eq127549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127549
  have eq210637 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210476
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq210476
    | exact resolve eq210476 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210476
  have eq210662 : x = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3729 eq210637
    | exact resolve eq210637 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210637
  have eq211955 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq210662 eq50
    | exact resolve eq50 eq210662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210662
  have eq212193 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq211955 x
       have i₂ := eq53 x x
       grind)
    | exact superpose eq53 eq211955
    | exact resolve eq211955 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211955
  have eq213112 : x = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1308 x
       have i₂ := eq212193
       grind)
    | exact superpose eq212193 eq1308
    | exact resolve eq1308 eq212193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq212193
  have eq213362 : x = (M.op y y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq213112
    | exact resolve eq213112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213112
  have eq214615 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq213362
       grind)
    | exact superpose eq213362 eq53
    | exact resolve eq53 eq213362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213362
  have eq214728 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq214615
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq214615
    | exact resolve eq214615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214615
  have eq214729 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq214728
  have eq215110 : ∀ X0 : G, (M.op (M.op X0 x) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq214729 eq16451
    | exact resolve eq16451 eq214729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16451
  have eq215131 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq214729 eq53
    | exact resolve eq53 eq214729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215256 : (M.op y (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3729 eq215131
    | exact resolve eq215131 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215131
  have eq215259 : y = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50 eq215110
    | exact resolve eq215110 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215110
  have eq217029 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq215256 eq215259
    | exact resolve eq215259 eq215256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215256 eq215259
  have eq217172 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq217029
  have eq217696 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq214729 eq217172
    | exact resolve eq217172 eq214729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217172
  have eq217803 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq217696
  have eq218217 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq217803
       grind)
    | exact superpose eq217803 eq47
    | exact resolve eq47 eq217803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq217803
  have eq218377 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq218217
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq218217
    | exact resolve eq218217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218217
  have eq218402 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3729 eq218377
    | exact resolve eq218377 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729 eq218377
  have eq218416 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq218402 eq50
    | exact resolve eq50 eq218402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq218402
  have eq218659 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq218416 x
       have i₂ := eq53 x x
       grind)
    | exact superpose eq53 eq218416
    | exact resolve eq218416 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218416
  have eq256456 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17787 x
       have i₂ := eq218659
       grind)
    | exact superpose eq218659 eq17787
    | exact resolve eq17787 eq218659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17787 eq218659
  have eq256656 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq256456
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq256456
    | exact resolve eq256456 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256456
  have eq256773 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq256656
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq256656
    | exact resolve eq256656 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256656
  have eq256774 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq256773
  have eq256918 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127503
       have i₂ := eq256774
       grind)
    | exact superpose eq256774 eq127503
    | exact resolve eq127503 eq256774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127503 eq256774
  have eq256930 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq256918
  have eq257430 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq256930 eq214729
    | exact resolve eq214729 eq256930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214729
  have eq257499 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq256930
  have eq257525 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq257430
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq257430
    | exact resolve eq257430 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257430
  have eq257526 : x = (M.op x y) ∨ x = y := by grind
  clear eq257525
  have eq257675 : x = (M.op x y) := by
    first
    | (have r₁ := eq257526
       have r₂ := eq257499
       grind)
    | exact resolve eq257526 eq257499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257499 eq257526
  have eq257677 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq257675 eq21
    | exact resolve eq21 eq257675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq257727 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq257675 eq210
    | exact resolve eq210 eq257675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq258004 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq257727
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq257727
    | exact resolve eq257727 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq257727
  have eq258049 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq257677
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq257677
    | exact resolve eq257677 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257677
  have eq258057 : x = (M.op y y) := by
    first
    | exact superpose eq257675 eq258004
    | exact resolve eq258004 eq257675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257675 eq258004
  have eq258060 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq258049 eq27
    | exact resolve eq27 eq258049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq258555 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq258057
       grind)
    | exact superpose eq258057 eq108
    | exact resolve eq108 eq258057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq258612 : y = (k x y) := by grind
  clear eq258057
  have eq258834 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq258555
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq258555
    | exact resolve eq258555 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258555
  have eq258864 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq258049 eq258834
    | exact resolve eq258834 eq258049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258834
  have eq259052 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq896 x y
       have i₂ := eq258612
       grind)
    | exact superpose eq258612 eq896
    | (have j0 := eq896 y y
       grind)
    | exact resolve eq896 eq258612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq258612
  have eq259055 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq259052
  have eq259061 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq259055
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq259055
    | exact resolve eq259055 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259055
  have eq259084 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq259061
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq259061
    | exact resolve eq259061 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259061
  have eq259107 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq259084
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq259084
    | exact resolve eq259084 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259084
  have eq259119 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq258049 eq259107
    | exact resolve eq259107 eq258049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259107
  have eq272746 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  have eq272883 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq259119
  have eq276287 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq272746 eq258864
    | exact resolve eq258864 eq272746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258864 eq272746
  have eq276330 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq276287
       have r₂ := eq272883
       grind)
    | exact resolve eq276287 eq272883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276287
  have eq276507 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq276330 eq53
    | exact resolve eq53 eq276330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq276330
  have eq276593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq258060 eq276507
    | exact resolve eq276507 eq258060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276507
  have eq276643 : x = y := by
    first
    | (have r₁ := eq276593
       have r₂ := eq28
       grind)
    | exact resolve eq276593 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276593
  have eq276667 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq276643
       grind)
    | exact superpose eq276643 eq25
    | exact resolve eq25 eq276643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq276643
  have eq277379 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq276667
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq276667
    | exact resolve eq276667 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq276667
  have eq277531 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq258049 eq277379
    | exact resolve eq277379 eq258049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258049 eq277379
  have eq278063 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq277531 eq258060
    | exact resolve eq258060 eq277531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258060
  have eq278077 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq277531 eq272883
    | (have r₁ := eq272883
       have r₂ := eq277531
       grind)
    | exact resolve eq272883 eq277531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272883 eq277531
  have eq278079 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq278077
  have eq279297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq278063 eq278079
    | exact resolve eq278079 eq278063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278063 eq278079
  have eq279298 : False := by grind
  exact eq279298

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq282 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq282
    | exact resolve eq282 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq282
  have eq344 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq62
    | exact resolve eq62 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       have j1 := eq345 X0 X1
       grind)
    | (have r₁ := eq344 X0 X1
       have r₂ := eq345 X0 X1
       grind)
    | exact resolve eq344 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq345
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq348
    | exact resolve eq348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq348 X0 (σ X1)
       grind)
    | exact superpose eq348 eq15
    | (have j1 := eq348 X0 (σ X1)
       grind)
    | exact resolve eq15 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq476 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq301 X1
       grind)
    | exact superpose eq301 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq457
  have eq494 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq446 (τ X0) X1
       grind)
    | exact superpose eq446 eq19
    | (have j1 := eq446 (τ X0) X1
       grind)
    | exact resolve eq19 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq446
  have eq720 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq494 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq778 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1158 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq476 x y
       grind)
    | exact superpose eq476 eq16
    | (have j1 := eq476 x y
       grind)
    | exact resolve eq16 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq1236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1158
       have i₂ := eq778 x y
       grind)
    | exact superpose eq778 eq1158
    | (have j1 := eq778 x y
       grind)
    | (have r₁ := eq1158
       have r₂ := eq778 x y
       grind)
    | exact resolve eq1158 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq1158
  have eq1237 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1236
  have eq1244 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq62 y
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq62
    | exact resolve eq62 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1246 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq346 y
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq346
    | exact resolve eq346 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1264 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq16
    | exact resolve eq16 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1282 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1264
       have i₂ := eq1244
       grind)
    | exact superpose eq1244 eq1264
    | exact resolve eq1264 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244 eq1264
  have eq1283 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1282
  have eq1284 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1283
  have eq1287 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq346 y
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq346
    | exact resolve eq346 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq1293 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq10
    | exact resolve eq10 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1337 : x = (M.op y y) := by
    first
    | (have i₁ := eq1293
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1293
    | exact resolve eq1293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1343 : y = (M.op x y) := by
    first
    | (have i₁ := eq62 y
       have i₂ := eq1337
       grind)
    | exact superpose eq1337 eq62
    | exact resolve eq62 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1337
  have eq1367 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1287
       grind)
    | exact superpose eq1287 eq16
    | exact resolve eq16 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1372 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1367
       have i₂ := eq1343
       grind)
    | exact superpose eq1343 eq1367
    | exact resolve eq1367 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq1367
  have eq1373 : False := by grind
  exact eq1373

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pxy_Equation1630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq109 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq109
    | exact resolve eq109 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq187 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
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
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq857 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq187
    | exact resolve eq187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq910 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq2465 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190 x y
       grind)
    | exact superpose eq190 eq16
    | (have j1 := eq190 x y
       grind)
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq4310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2465
       have i₂ := eq910 x y
       grind)
    | exact superpose eq910 eq2465
    | (have j1 := eq910 x y
       grind)
    | (have r₁ := eq2465
       have r₂ := eq910 x y
       grind)
    | (have r₁ := eq2465
       have r₂ := eq910 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2465
       have r₂ := eq910 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2465 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq2465
  have eq4311 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4310
  have eq4313 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4311
       grind)
    | exact superpose eq4311 eq16
    | exact resolve eq16 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311
  have eq4314 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4313
       have r₂ := eq23 x
       grind)
    | exact resolve eq4313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq4319 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq109 y
       have i₂ := eq4314
       grind)
    | exact superpose eq4314 eq109
    | exact resolve eq109 eq4314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4320 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110 y
       have i₂ := eq4314
       grind)
    | exact superpose eq4314 eq110
    | exact resolve eq110 eq4314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4314
  have eq4353 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4320
       grind)
    | exact superpose eq4320 eq16
    | exact resolve eq16 eq4320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq4374 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4353
       have i₂ := eq4319
       grind)
    | exact superpose eq4319 eq4353
    | exact resolve eq4353 eq4319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319 eq4353
  have eq4375 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4374
  have eq4376 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4375
  have eq4378 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4376
       grind)
    | exact superpose eq4376 eq10
    | exact resolve eq10 eq4376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4376
  have eq4426 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4378
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4378
    | exact resolve eq4378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4378
  have eq4428 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4426
       grind)
    | exact superpose eq4426 eq16
    | exact resolve eq16 eq4426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4426
  have eq4429 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4428
       have r₂ := eq23 x
       grind)
    | exact resolve eq4428 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4428
  have eq4433 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110 y
       have i₂ := eq4429
       grind)
    | exact superpose eq4429 eq110
    | exact resolve eq110 eq4429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq4443 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4429
       grind)
    | exact superpose eq4429 eq10
    | exact resolve eq10 eq4429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4429
  have eq4491 : x = (M.op y y) := by
    first
    | (have i₁ := eq4443
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4443
    | exact resolve eq4443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4498 : y = (M.op x y) := by
    first
    | (have i₁ := eq109 y
       have i₂ := eq4491
       grind)
    | exact superpose eq4491 eq109
    | exact resolve eq109 eq4491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq4491
  have eq4537 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4433
       grind)
    | exact superpose eq4433 eq16
    | exact resolve eq16 eq4433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4433
  have eq4542 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4537
       have i₂ := eq4498
       grind)
    | exact superpose eq4498 eq4537
    | exact resolve eq4537 eq4498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498 eq4537
  have eq4543 : False := by grind
  exact eq4543

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65
    | exact resolve eq65 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq241 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq248 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq241 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq241 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq241 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq241
  have eq254 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq248
    | exact resolve eq248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq248 (σ X1) X0
       grind)
    | exact superpose eq248 eq15
    | (have j1 := eq248 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq268 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq254 X0 (τ X1)
       grind)
    | exact superpose eq254 eq18
    | (have j1 := eq254 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq254
  have eq726 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq268
    | exact resolve eq268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq761 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq726
    | (have j0 := eq726 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq726 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1780 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq259 x y
       grind)
    | exact superpose eq259 eq16
    | (have j1 := eq259 x y
       grind)
    | exact resolve eq16 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1868 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1780
       have i₂ := eq761 y x
       grind)
    | exact superpose eq761 eq1780
    | (have j1 := eq761 (σ x) (σ y)
       grind)
    | (have r₁ := eq1780
       have r₂ := eq761 y x
       grind)
    | (have r₁ := eq1780
       have r₂ := eq761 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1780
       have r₂ := eq761 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1780 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq1780
  have eq1869 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1868
  have eq1873 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1869
       grind)
    | exact superpose eq1869 eq10
    | exact resolve eq10 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1918 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1873
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1873
    | exact resolve eq1873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq1919 : x = y := by grind
  clear eq1918
  have eq2192 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1919
       grind)
    | exact superpose eq1919 eq16
    | exact resolve eq16 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq2193 : False := by grind
  exact eq2193

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
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
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 x) (M.op (M.op x y) y)) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq43
    | exact resolve eq43 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq75 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq80
    | (have j0 := eq80 (σ X0) (σ X1)
       grind)
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq104
    | exact resolve eq104 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq108
    | exact resolve eq108 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq108
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq103
    | (have j1 := eq80 y x
       grind)
    | exact resolve eq103 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq127 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq128 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq80
    | (have j0 := eq80 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq141
    | exact resolve eq141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq145 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq142
       have r₂ := eq27
       grind)
    | exact resolve eq142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq147 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq145
    | exact resolve eq145 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq276 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op (M.op (M.op x y) y) X1) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147 eq54
    | exact resolve eq54 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ x))) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ y) (σ y)) X1) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq298 eq14
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq306 (M.op X0 (M.op sF3 sF3)) x
       have i₂ := eq14 X0 (M.op sF3 sF3) x
       grind)
    | exact superpose eq14 eq306
    | exact resolve eq306 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq945 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) ≠ X0 ∨ (k (M.op X1 (M.op (M.op X2 X3) X3)) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 (M.op (M.op X2 X3) X3)) (M.op X1 (M.op X0 X2))
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq13
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1222 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147 eq128
    | (have r₁ := eq128
       have r₂ := eq147
       grind)
    | exact resolve eq128 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq1223 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1222
  have eq1316 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) X2) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq14
    | (have j1 := eq86 X0 X1
       grind)
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq6630 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1223 eq120
    | exact resolve eq120 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq6633 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq6630
  have eq6688 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6633 eq66
    | exact resolve eq66 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq6633
  have eq6730 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq6688
       have r₂ := eq147
       grind)
    | exact resolve eq6688 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq6688
  have eq6860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6730 eq120
    | exact resolve eq120 eq6730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq6730
  have eq6863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq6860
  have eq6867 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6863
       have r₂ := eq27
       grind)
    | exact resolve eq6863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6863
  have eq6869 : (τ (σ (M.op x y))) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6867 eq134
    | exact resolve eq134 eq6867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq6870 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6867 eq298
    | exact resolve eq298 eq6867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq6876 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ x)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6867 eq470
    | exact resolve eq470 eq6867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq6867
  have eq6939 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6876
  have eq6945 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6870 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870
  have eq6947 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq6869
    | exact resolve eq6869 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6869
  have eq6995 : x = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq6947
       grind)
    | exact superpose eq6947 eq50
    | exact resolve eq50 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7001 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (M.op x y) y) X1) X1)) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 y y X1
       have i₂ := eq6947
       grind)
    | exact superpose eq6947 eq52
    | exact resolve eq52 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq7014 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq276 eq7001
    | exact resolve eq7001 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq7001
  have eq7474 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6939 eq54
    | exact resolve eq54 eq6939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq6939
  have eq7558 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6995 eq945
    | exact resolve eq945 eq6995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq6995
  have eq7583 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq7558
       grind)
    | exact superpose eq7558 eq75
    | exact resolve eq75 eq7558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7558
  have eq7606 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq7583
    | exact resolve eq7583 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7583
  have eq7623 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7606 eq6945
    | exact resolve eq6945 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7627 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7606 eq14
    | exact resolve eq14 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7642 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq7623
  have eq7662 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7642 eq14
    | exact resolve eq14 eq7642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7838 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6947
       have i₂ := eq7014 y
       grind)
    | exact superpose eq7014 eq6947
    | exact resolve eq6947 eq7014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7014
  have eq7877 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq7838
  have eq7914 : y = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq7877
       grind)
    | exact superpose eq7877 eq53
    | exact resolve eq53 eq7877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq7877
  have eq9346 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1322 x y
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq1322
    | (have j0 := eq1322 x y
       grind)
    | exact resolve eq1322 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq9361 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9346
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9346
    | exact resolve eq9346 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9392 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9361
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9361
    | exact resolve eq9361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9361
  have eq9420 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9392
    | exact resolve eq9392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9392
  have eq9438 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9420
    | exact resolve eq9420 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9420
  have eq24973 : ∀ X0 : G, (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op (M.op y X0) X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7914 eq958
    | exact resolve eq958 eq7914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7914
  have eq25137 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) (M.op (M.op y X0) X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24973 X0
       grind)
    | (have r₁ := eq24973 X0
       have r₂ := eq6947
       grind)
    | exact resolve eq24973 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947 eq24973
  have eq25247 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq25137
    | exact resolve eq25137 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq25267 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25247
       grind)
    | exact superpose eq25247 eq44
    | exact resolve eq44 eq25247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq25247
  have eq25281 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq25267
    | exact resolve eq25267 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25267
  have eq25308 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq25281
       have i₂ := eq80 sF2 sF3
       grind)
    | exact superpose eq80 eq25281
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq25281 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq25281
  have eq29993 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7606 eq7627
    | exact resolve eq7627 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606 eq7627
  have eq30155 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq29993
  have eq30374 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30155 eq301
    | exact resolve eq301 eq30155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq30155
  have eq36872 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7642 eq7662
    | exact resolve eq7662 eq7642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7642 eq7662
  have eq37045 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq36872
  have eq43586 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7474 eq30374
    | exact resolve eq30374 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7474 eq30374
  have eq43641 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq43586
  have eq61728 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq25308 eq6945
    | exact resolve eq6945 eq25308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25308
  have eq61770 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq61728
  have eq61908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq61770 eq37045
    | exact resolve eq37045 eq61770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37045 eq61770
  have eq61962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq61908
  have eq61965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq61962
    | exact resolve eq61962 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61962
  have eq61966 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61965
       have r₂ := eq27
       grind)
    | exact resolve eq61965 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61965
  have eq62001 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61966 eq6945
    | exact resolve eq6945 eq61966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6945 eq61966
  have eq62041 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq62001
  have eq62081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62041 eq43641
    | exact resolve eq43641 eq62041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43641 eq62041
  have eq62156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq62081
  have eq62167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq62156
    | exact resolve eq62156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62156
  have eq62172 : y = (M.op x y) := by
    first
    | (have r₁ := eq62167
       have r₂ := eq27
       grind)
    | exact resolve eq62167 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62167
  have eq62173 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq62172 eq20
    | exact resolve eq20 eq62172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq62175 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | exact superpose eq62172 eq50
    | exact resolve eq50 eq62172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq62184 : y ≠ y ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq62172 eq127
    | (have r₁ := eq127
       have r₂ := eq62172
       grind)
    | exact resolve eq127 eq62172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq62286 : (k y x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq62184
  have eq62351 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq62173
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62173
    | exact resolve eq62173 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62173
  have eq62372 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq62351 eq26
    | exact resolve eq26 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq62550 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62351 eq9438
    | exact resolve eq9438 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9438
  have eq62649 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq62550
       have r₂ := eq27
       grind)
    | exact resolve eq62550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62550
  have eq62837 : ∀ X0 X1 : G, y ≠ (M.op x x) ∨ y = (k (M.op (M.op y X0) (M.op (M.op X0 X1) X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq958 y (M.op y X0) X0 x
       have i₂ := eq62175 X0
       grind)
    | exact superpose eq62175 eq958
    | exact resolve eq958 eq62175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq62175
  have eq62934 : y ≠ (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq62837 x x
       have i₂ := eq14 y x x
       grind)
    | exact superpose eq14 eq62837
    | exact resolve eq62837 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62837
  have eq64708 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1316 y x X0
       have i₂ := eq62286
       grind)
    | exact superpose eq62286 eq1316
    | (have j0 := eq1316 y x x
       grind)
    | exact resolve eq1316 eq62286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq62286
  have eq64723 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq64708 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq64708
    | (have j0 := eq64708 X0
       grind)
    | exact resolve eq64708 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64708
  have eq64744 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ (M.op x y)) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq62351 eq64723
    | exact resolve eq64723 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64723
  have eq64765 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ (M.op x y)) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq64744 X0
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq64744
    | exact resolve eq64744 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq64744
  have eq64783 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op (σ (M.op x y)) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq62351 eq64765
    | exact resolve eq64765 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64765
  have eq64793 : (σ x) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64783 x
       have i₂ := eq14 sF1 sF1 x
       grind)
    | exact superpose eq14 eq64783
    | exact resolve eq64783 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64783
  have eq64803 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64793
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64793
    | exact resolve eq64793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64793
  have eq64812 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64803
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq64803
    | exact resolve eq64803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64803
  have eq64820 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq62351 eq64812
    | exact resolve eq64812 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64812
  have eq64828 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64820
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64820
    | exact resolve eq64820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64820
  have eq64835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq62372 eq64828
    | exact resolve eq64828 eq62372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64828
  have eq64839 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq64835
       have r₂ := eq27
       grind)
    | exact resolve eq64835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64835
  have eq65184 : y ≠ y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq62934
       have i₂ := eq64839
       grind)
    | exact superpose eq64839 eq62934
    | (have r₁ := eq62934
       have r₂ := eq64839
       grind)
    | exact resolve eq62934 eq64839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62934 eq64839
  have eq65244 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq65184
  have eq65318 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq65244
       grind)
    | exact superpose eq65244 eq103
    | exact resolve eq103 eq65244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq65244
  have eq65366 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq62351 eq65318
    | exact resolve eq65318 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65318
  have eq65386 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq65366
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65366
    | exact resolve eq65366 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq65366
  have eq65405 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq62351 eq65386
    | exact resolve eq65386 eq62351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62351 eq65386
  have eq65419 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq65405
       have r₂ := eq62649
       grind)
    | exact resolve eq65405 eq62649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62649 eq65405
  have eq65463 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq65419 eq28
    | exact resolve eq28 eq65419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq65724 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq65419 eq62372
    | exact resolve eq62372 eq65419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62372
  have eq65795 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq65463
    | exact resolve eq65463 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq65463
  have eq65835 : x = y := by
    first
    | exact superpose eq62172 eq65795
    | exact resolve eq65795 eq62172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65795
  have eq67243 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq65835
       grind)
    | exact superpose eq65835 eq18
    | exact resolve eq18 eq65835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq67570 : y = (M.op x x) := by
    first
    | exact superpose eq62172 eq67243
    | exact resolve eq67243 eq62172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62172 eq67243
  have eq67730 : x = (M.op x x) := by
    first
    | (have i₁ := eq67570
       have i₂ := eq65835
       grind)
    | exact superpose eq65835 eq67570
    | exact resolve eq67570 eq65835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65835 eq67570
  have eq68081 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq67730
       grind)
    | exact superpose eq67730 eq75
    | exact resolve eq75 eq67730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq67730
  have eq68219 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq65419 eq68081
    | exact resolve eq68081 eq65419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68081
  have eq68262 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65724 eq68219
    | exact resolve eq68219 eq65724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65724 eq68219
  have eq68295 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq68262
    | exact resolve eq68262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq68262
  have eq68326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65419 eq68295
    | exact resolve eq68295 eq65419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65419 eq68295
  have eq68350 : False := by grind
  exact eq68350

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_y_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op X0 x) (M.op (M.op x y) y)) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) ≠ X0 ∨ (M.op X0 X1) = (k (M.op (M.op X1 X2) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X2) X2) (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 X2) X2) (M.op X0 X1)
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X2) X2) (M.op (M.op (M.op X1 X2) X2) X1)
       have r₂ := eq14 (M.op (M.op X1 X2) X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq83 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq82
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq16
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq84 eq16
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq116 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq147 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq161 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq208 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 x)) (M.op X0 (M.op (M.op x y) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op (M.op (M.op x y) y) X1) X1)) := by
    intro X0 X1
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq347 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq99 x
       grind)
    | exact superpose eq99 eq43
    | (have j1 := eq99 x
       grind)
    | exact resolve eq43 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq348 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq83
    | (have j1 := eq99 y
       grind)
    | exact resolve eq83 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq469 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq231 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq231
    | (have j0 := eq231 X0 y
       grind)
    | exact resolve eq231 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq231
    | (have j0 := eq231 X0 (M.op x y)
       grind)
    | exact resolve eq231 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq61
    | exact resolve eq61 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq57 eq61
    | exact resolve eq61 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 (M.op (M.op x y) y)))) (M.op X2 (M.op X0 x))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq561 eq61
    | exact resolve eq61 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq631 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (k (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62 (M.op (M.op X0 X1) X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq759 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq69 X1 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq780 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq787 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq780
    | (have j0 := eq780 X0 X1
       grind)
    | exact resolve eq780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq8385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8386 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8385
    | exact resolve eq8385 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8385
  have eq8397 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8386
       have r₂ := eq27
       grind)
    | exact resolve eq8386 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386
  have eq8399 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8397
    | exact resolve eq8397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8397
  have eq8401 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8399
    | exact resolve eq8399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8399
  have eq8538 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8401 eq14
    | exact resolve eq14 eq8401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8401
  have eq8556 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57 eq8538
    | exact resolve eq8538 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8538
  have eq8562 : x = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq8556
       grind)
    | exact superpose eq8556 eq56
    | exact resolve eq56 eq8556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8567 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq8556
       grind)
    | exact superpose eq8556 eq14
    | exact resolve eq14 eq8556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8569 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (M.op x y) y) X1) X1)) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 y y X1
       have i₂ := eq8556
       grind)
    | exact superpose eq8556 eq58
    | exact resolve eq58 eq8556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq8584 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq209 eq8569
    | exact resolve eq8569 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq8569
  have eq8585 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq8567
    | exact resolve eq8567 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8567
  have eq8588 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8585 eq51
    | (have r₁ := eq51
       have r₂ := eq8585
       grind)
    | exact resolve eq51 eq8585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8585
  have eq8599 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq8588
  have eq8620 : (τ (σ x)) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8599 eq92
    | exact resolve eq92 eq8599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq8621 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8599 eq96
    | exact resolve eq96 eq8599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8599
  have eq8629 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8621
  have eq8638 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq8620
    | exact resolve eq8620 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8620
  have eq8643 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8638
       have r₂ := eq50
       grind)
    | exact resolve eq8638 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8649 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq8643
       grind)
    | exact superpose eq8643 eq82
    | exact resolve eq82 eq8643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8643
  have eq8664 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8649
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8649
    | exact resolve eq8649 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649
  have eq8682 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8664 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8664
  have eq8683 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq8682
    | exact resolve eq8682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8682
  have eq8694 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq8683
    | exact resolve eq8683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8683
  have eq8696 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq8694
    | exact resolve eq8694 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8694
  have eq10057 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8556
       have i₂ := eq8584 y
       grind)
    | exact superpose eq8584 eq8556
    | exact resolve eq8556 eq8584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8556 eq8584
  have eq10077 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq10057
  have eq10088 : y = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 y
       have i₂ := eq10077
       grind)
    | exact superpose eq10077 eq59
    | exact resolve eq59 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq10077
  have eq10382 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq8629
       grind)
    | exact superpose eq8629 eq14
    | exact resolve eq14 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq10405 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq56 eq10382
    | exact resolve eq10382 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10382
  have eq10406 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10405
  have eq10416 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10406 eq29
    | exact resolve eq29 eq10406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10406
  have eq10537 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq10416
    | exact resolve eq10416 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10416
  have eq10538 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq10537
  have eq10540 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq10538 eq28
    | exact resolve eq28 eq10538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10557 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq10538 eq96
    | exact resolve eq96 eq10538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq10538
  have eq10619 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10557
  have eq10666 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq10540
    | exact resolve eq10540 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10540
  have eq10667 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10666 eq20
    | exact resolve eq20 eq10666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10669 : y ≠ y ∨ x = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10666 eq50
    | (have r₁ := eq50
       have r₂ := eq10666
       grind)
    | exact resolve eq50 eq10666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq10670 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10666 eq56
    | exact resolve eq56 eq10666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10677 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10666 eq116
    | exact resolve eq116 eq10666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq10725 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10666 eq470
    | exact resolve eq470 eq10666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq10666
  have eq10735 : x = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq10669
  have eq10736 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10725 X0
       have i₂ := eq469 X0
       grind)
    | exact superpose eq469 eq10725
    | exact resolve eq10725 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq10725
  have eq10779 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10677 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq10677
    | exact resolve eq10677 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq10677
  have eq10786 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10667
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10667
    | exact resolve eq10667 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10667
  have eq11023 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq82
    | exact resolve eq82 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11041 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11023
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11023
    | exact resolve eq11023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11023
  have eq11139 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10786 eq11041
    | exact resolve eq11041 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq11159 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq11139
  have eq11657 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq161 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq161
    | (have j0 := eq161 y
       grind)
    | exact resolve eq161 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq11695 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11657
    | exact resolve eq11657 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11657
  have eq11711 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11695
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq11695
    | exact resolve eq11695 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq11695
  have eq11716 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11711
    | exact resolve eq11711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711
  have eq11717 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11716
    | exact resolve eq11716 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11716
  have eq11735 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10779 eq231
    | exact resolve eq231 eq10779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10779
  have eq11843 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11735 x
       have i₂ := eq231 sF1 x
       grind)
    | exact superpose eq231 eq11735
    | exact resolve eq11735 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq11735
  have eq11848 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq11843
    | exact resolve eq11843 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11843
  have eq11851 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq11848
    | exact resolve eq11848 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11848
  have eq16024 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       have j1 := eq776 X1 X0
       grind)
    | (have r₁ := eq787 X1 X0
       have r₂ := eq776 X0 X1
       grind)
    | (have r₁ := eq787 X1 X1
       have r₂ := eq776 X1 X1
       grind)
    | exact resolve eq787 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq787
  have eq16025 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq16024 X0 X1
       have j1 := eq777 X1 X0
       grind)
    | (have r₁ := eq16024 X1 X1
       have r₂ := eq777 X0 X1
       grind)
    | (have r₁ := eq16024 X1 X1
       have r₂ := eq777 X0 X1
       grind)
    | exact resolve eq16024 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq16024
  have eq16546 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq16025 X0 X1
       grind)
    | exact superpose eq16025 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq16025 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq16025 X0 X1
       grind)
    | exact resolve eq13 eq16025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16568 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16025 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16025
  have eq16573 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16546 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq16546 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq16546 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16546
  have eq16585 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16573 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16573
    | (have j0 := eq16573 X0 X1
       grind)
    | exact resolve eq16573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq37375 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10619 eq110
    | exact resolve eq110 eq10619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10619
  have eq37406 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq37375
    | exact resolve eq37375 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37375
  have eq39921 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq8696 eq14
    | exact resolve eq14 eq8696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8696
  have eq39952 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57 eq39921
    | exact resolve eq39921 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39921
  have eq39953 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq39952
  have eq39956 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq39953 eq27
    | exact resolve eq27 eq39953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10786 eq39956
    | (have r₁ := eq39956
       have r₂ := eq10786
       grind)
    | exact resolve eq39956 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39956
  have eq40001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq40000
  have eq40002 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq40001
  have eq40017 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40002 eq562
    | exact resolve eq562 eq40002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40053 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq40017
    | (have j0 := eq40017 X0
       grind)
    | exact resolve eq40017 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40017
  have eq40067 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40002 eq40053
    | exact resolve eq40053 eq40002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40053
  have eq40124 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq40067 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40067
  have eq40202 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f40202_16 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      grind
    have f40202_22 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f40202_25 : X1 ≠ (M.op (M.op X1 X0) X0) := by grind
    have f40202_26 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f40202_27 : x ≠ y := by grind
    have f40202_28 : x ≠ (M.op x y) := by grind
    have f40202_29 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f40202_16 X0
         grind)
      | (have r₁ := f40202_16 X0
         have r₂ := f40202_26
         grind)
      | exact resolve f40202_16 f40202_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40202_30 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f40202_29 X0
         grind)
      | (have r₁ := f40202_29 X0
         have r₂ := f40202_27
         grind)
      | exact resolve f40202_29 f40202_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40202_31 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f40202_30 X0
         grind)
      | (have r₁ := f40202_30 X0
         have r₂ := f40202_28
         grind)
      | exact resolve f40202_30 f40202_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40202_43 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f40202_22 X1 X0 (σ x)
         have i₂ := f40202_31 X0
         grind)
      | exact superpose f40202_31 f40202_22
      | exact resolve f40202_22 f40202_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40202_49 : X1 ≠ X1 := by
      first
      | (have i₁ := f40202_25
         have i₂ := f40202_43 X0 X1
         grind)
      | exact superpose f40202_43 f40202_25
      | (have r₁ := f40202_25
         have r₂ := f40202_43 X0 X1
         grind)
      | exact resolve f40202_25 f40202_43
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40202_53 : False := by grind
    exact f40202_53
  have eq40254 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq40124 eq10670
    | exact resolve eq10670 eq40124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40124
  have eq40307 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq40254
  have eq40584 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq348
       have i₂ := eq40307
       grind)
    | exact superpose eq40307 eq348
    | exact resolve eq348 eq40307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40307
  have eq40645 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq40584
  have eq40682 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40645
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40645
    | exact resolve eq40645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40645
  have eq40896 : (τ (σ x)) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40682 eq10736
    | exact resolve eq10736 eq40682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736 eq40682
  have eq40904 : (τ (σ x)) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq40896
  have eq40920 : (τ (σ x)) = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq110 eq40904
    | exact resolve eq40904 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq40904
  have eq40931 : x = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq40920
    | exact resolve eq40920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40920
  have eq42912 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10786 eq11717
    | exact resolve eq11717 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11717
  have eq42974 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq42912
       have r₂ := eq27
       grind)
    | exact resolve eq42912 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42912
  have eq42989 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq42974 eq11159
    | exact resolve eq11159 eq42974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11159 eq42974
  have eq43021 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42989
  have eq43032 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43021 eq12
    | exact resolve eq12 eq43021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43021
  have eq43062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43032
  have eq43066 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43062
       have r₂ := eq27
       grind)
    | exact resolve eq43062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43062
  have eq43072 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43066 eq147
    | exact resolve eq147 eq43066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq43066
  have eq43125 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43072 eq11851
    | exact resolve eq11851 eq43072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11851 eq43072
  have eq43127 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43125
  have eq49259 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40931 eq16585
    | exact resolve eq16585 eq40931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40931
  have eq49260 : (σ y) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43127 eq16585
    | exact resolve eq16585 eq43127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16585 eq43127
  have eq49562 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49260
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq49260
    | exact resolve eq49260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49260
  have eq49563 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49259
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq49259
    | exact resolve eq49259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49259
  have eq49733 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49562
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq49562
    | exact resolve eq49562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49562
  have eq49734 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49563
    | exact resolve eq49563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49563
  have eq49813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49733
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq49733
    | exact resolve eq49733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49733
  have eq49814 : (σ x) = (σ (M.op x y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq49734
    | exact resolve eq49734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49734
  have eq49886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq49813
    | exact resolve eq49813 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49813
  have eq49887 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49814
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49814
    | exact resolve eq49814 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49814
  have eq49888 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq49887
  have eq49954 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq49886
       have r₂ := eq27
       grind)
    | exact resolve eq49886 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49886
  have eq49960 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq39953 eq49954
    | (have r₁ := eq49954
       have r₂ := eq39953
       grind)
    | exact resolve eq49954 eq39953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39953 eq49954
  have eq49964 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq49960
  have eq49965 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49964
  have eq49980 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq49965 eq562
    | exact resolve eq562 eq49965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50029 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq49980
    | (have j0 := eq49980 X0
       grind)
    | exact resolve eq49980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49980
  have eq54146 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq49965 eq50029
    | exact resolve eq50029 eq49965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49965 eq50029
  have eq54217 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq54146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54146
  have eq54375 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq54217 eq57
    | exact resolve eq57 eq54217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54217
  have eq54591 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16568 x y
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq16568
    | (have j0 := eq16568 x y
       grind)
    | exact resolve eq16568 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10735
  have eq55019 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54591
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54591
    | exact resolve eq54591 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54591
  have eq55240 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55019
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55019
    | exact resolve eq55019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55019
  have eq55421 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55240
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55240
    | exact resolve eq55240 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55240
  have eq55506 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55421
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55421
    | exact resolve eq55421 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55421
  have eq55552 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq55506
    | exact resolve eq55506 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55506
  have eq55554 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10786 eq55552
    | exact resolve eq55552 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55552
  have eq55558 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq55554
  have eq55559 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq55558
       have r₂ := eq27
       grind)
    | exact resolve eq55558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55558
  have eq55945 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq40002 eq54375
    | exact resolve eq54375 eq40002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40002 eq54375
  have eq56003 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq55945
  have eq56033 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq56003
       have r₂ := eq49888
       grind)
    | exact resolve eq56003 eq49888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49888 eq56003
  have eq56046 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq56033
       have r₂ := eq55559
       grind)
    | exact resolve eq56033 eq55559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56033
  have eq56054 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq56046
    | exact resolve eq56046 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56046
  have eq56069 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq56054 eq562
    | exact resolve eq562 eq56054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq56127 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq56069
    | (have j0 := eq56069 X0
       grind)
    | exact resolve eq56069 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56069
  have eq56143 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq56054 eq56127
    | exact resolve eq56127 eq56054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56054 eq56127
  have eq56218 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq56143 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56143
  have eq56378 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56218 eq10670
    | exact resolve eq10670 eq56218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10670 eq56218
  have eq56437 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq56378
  have eq56757 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq348
       have i₂ := eq56437
       grind)
    | exact superpose eq56437 eq348
    | exact resolve eq348 eq56437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq56437
  have eq56824 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq56757
  have eq56864 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56824
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56824
    | exact resolve eq56824 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56824
  have eq57109 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq56864
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq56864
    | (have j1 := eq99 (σ y)
       grind)
    | exact resolve eq56864 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59166 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X0 (M.op X2 x)) (M.op X2 (M.op (M.op x y) y)))) X0) = X1 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq591 X2 X1 (M.op X0 (M.op X2 x))
       have i₂ := eq40202 (M.op X2 x) X0
       grind)
    | exact superpose eq40202 eq591
    | exact resolve eq591 eq40202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq40202
  have eq59340 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X0 (M.op X2 x)) (M.op X2 (M.op (M.op x y) y)))) X0) = X1 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq59166 X0 X1 X2
       grind)
    | (have r₁ := eq59166 X0 X1 X2
       have r₂ := eq55559
       grind)
    | exact resolve eq59166 eq55559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55559 eq59166
  have eq59413 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq208 eq59340
    | exact resolve eq59340 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq59340
  have eq184770 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq57109 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq57109
       grind)
    | exact resolve eq13 eq57109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184811 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq57109
  have eq184814 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq184770
  have eq184957 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq184814 eq56864
    | exact resolve eq56864 eq184814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56864 eq184814
  have eq184997 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq184957
  have eq185024 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq184997
       have r₂ := eq184811
       grind)
    | exact resolve eq184997 eq184811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184811 eq184997
  have eq185111 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq185024 eq59413
    | exact resolve eq59413 eq185024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59413 eq185024
  have eq185112 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq185111
  have eq185126 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq185112
    | exact resolve eq185112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185112
  have eq185205 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq185126 eq27
    | exact resolve eq27 eq185126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185126
  have eq185559 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq185205
       have r₂ := eq10786
       grind)
    | exact resolve eq185205 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10786 eq185205
  have eq185563 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq185559 eq20
    | exact resolve eq20 eq185559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185631 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq185559 eq561
    | exact resolve eq561 eq185559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq185714 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq185559 eq8562
    | exact resolve eq8562 eq185559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8562
  have eq185719 : y = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq185559 eq10088
    | exact resolve eq10088 eq185559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10088
  have eq185740 : x = (k y x) ∨ x = (M.op y y) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq185559 eq37406
    | exact resolve eq37406 eq185559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37406
  have eq185745 : x = (k y x) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq185740
  have eq185767 : y = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq185719
  have eq185773 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq185714
  have eq185775 : y = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq185767
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq185767
    | exact resolve eq185767 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185767
  have eq185776 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq185773
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq185773
    | exact resolve eq185773 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185773
  have eq185857 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq185631 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq185631
    | (have j0 := eq185631 X0
       grind)
    | exact resolve eq185631 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185631
  have eq185920 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq185563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq185563
    | exact resolve eq185563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185563
  have eq185927 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq185920 eq26
    | exact resolve eq26 eq185920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185920
  have eq186543 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq185559 eq185857
    | exact resolve eq185857 eq185559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185857
  have eq186646 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq186543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186543
  have eq188330 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq186646 X0
       grind)
    | exact superpose eq186646 eq14
    | exact resolve eq14 eq186646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188346 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq631 X0 x
       have i₂ := eq186646 X0
       grind)
    | exact superpose eq186646 eq631
    | exact resolve eq631 eq186646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq188411 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq186646 sF3
       grind)
    | exact superpose eq186646 eq57
    | exact resolve eq57 eq186646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq186646
  have eq190739 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq185927 eq188330
    | exact resolve eq188330 eq185927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185927
  have eq191317 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by grind
  clear eq190739
  have eq191621 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ y) X0) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq191317 eq14
    | exact resolve eq14 eq191317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191317
  have eq234416 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16568 x y
       have i₂ := eq185745
       grind)
    | exact superpose eq185745 eq16568
    | (have j0 := eq16568 x y
       grind)
    | exact resolve eq16568 eq185745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185745
  have eq234436 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq234416
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq234416
    | exact resolve eq234416 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234416
  have eq234452 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq234436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq234436
    | exact resolve eq234436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234436
  have eq234454 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq234452
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq234452
    | exact resolve eq234452 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234452
  have eq234456 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq234454
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq234454
    | exact resolve eq234454 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234454
  have eq234458 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq26 eq234456
    | exact resolve eq234456 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234456
  have eq247500 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq185776 eq185775
    | exact resolve eq185775 eq185776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185775 eq185776
  have eq247569 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq247500
  have eq308914 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq234458
       have r₂ := eq247569
       grind)
    | exact resolve eq234458 eq247569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234458
  have eq308961 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq188346 y
       have i₂ := eq308914
       grind)
    | exact superpose eq308914 eq188346
    | exact resolve eq188346 eq308914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188346 eq308914
  have eq309020 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq308961
  have eq310493 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16568 x y
       have i₂ := eq309020
       grind)
    | exact superpose eq309020 eq16568
    | (have j0 := eq16568 x y
       grind)
    | exact resolve eq16568 eq309020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309020
  have eq310517 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq310493
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq310493
    | exact resolve eq310493 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310493
  have eq310540 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq310517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq310517
    | exact resolve eq310517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310517
  have eq310549 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq310540
       have r₂ := eq247569
       grind)
    | exact resolve eq310540 eq247569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247569 eq310540
  have eq310557 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq310549
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq310549
    | exact resolve eq310549 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310549
  have eq310563 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq310557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq310557
    | exact resolve eq310557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310557
  have eq310571 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq310563
    | exact resolve eq310563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310563
  have eq310572 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq310571
  have eq310766 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq310572 eq188411
    | exact resolve eq188411 eq310572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188411
  have eq310921 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq310766
  have eq311431 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq310921 eq191621
    | exact resolve eq191621 eq310921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191621 eq310921
  have eq311502 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq311431
  have eq311561 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq26 eq311502
    | exact resolve eq311502 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311502
  have eq312393 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq311561 eq188330
    | exact resolve eq188330 eq311561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188330 eq311561
  have eq312394 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq312393
  have eq313005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq312394 eq12
    | exact resolve eq12 eq312394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312394
  have eq313061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq313005
  have eq313098 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have r₁ := eq313061
       have r₂ := eq27
       grind)
    | exact resolve eq313061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313061
  have eq313591 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq310572 eq313098
    | exact resolve eq313098 eq310572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310572 eq313098
  have eq313620 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq313591
  have eq313710 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq313620 eq104
    | exact resolve eq104 eq313620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq313620
  have eq313811 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq313710
    | exact resolve eq313710 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq313710
  have eq313820 : (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq313811
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq313811
    | (have j1 := eq99 y
       grind)
    | exact resolve eq313811 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646917 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq313820
       grind)
    | exact superpose eq313820 eq14
    | exact resolve eq14 eq313820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313820
  have eq647046 : x = y ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq56 eq646917
    | exact resolve eq646917 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq646917
  have eq647047 : y = (M.op y y) ∨ x = y := by grind
  clear eq647046
  have eq647117 : y ≠ y ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq647047
       grind)
    | exact superpose eq647047 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq647047
       grind)
    | exact resolve eq13 eq647047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647047
  have eq647214 : y = (k y y) ∨ x = y := by grind
  clear eq647117
  have eq647305 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq313811
       have i₂ := eq647214
       grind)
    | exact superpose eq647214 eq313811
    | exact resolve eq313811 eq647214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313811 eq647214
  have eq647352 : y = (M.op x y) ∨ x = y := by grind
  clear eq647305
  have eq647857 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq647352 eq185559
    | exact resolve eq185559 eq647352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185559 eq647352
  have eq648294 : x = y := by grind
  clear eq647857
  have eq648662 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq648294
       grind)
    | exact superpose eq648294 eq18
    | exact resolve eq18 eq648294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq648663 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq648294
       grind)
    | exact superpose eq648294 eq24
    | exact resolve eq24 eq648294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq648294
  have eq649053 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq648663
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq648663
    | exact resolve eq648663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648663
  have eq649083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq649053 eq26
    | exact resolve eq26 eq649053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq649923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq347
       have i₂ := eq648662
       grind)
    | exact superpose eq648662 eq347
    | exact resolve eq347 eq648662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq649961 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq648662
       grind)
    | exact superpose eq648662 eq13
    | (have j0 := eq13 x x
       grind)
    | exact resolve eq13 eq648662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648662
  have eq650128 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq649923
    | exact resolve eq649923 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649923
  have eq664866 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq650128 eq99
    | (have j0 := eq99 (σ x)
       grind)
    | exact resolve eq99 eq650128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq664898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649083 eq664866
    | exact resolve eq664866 eq649083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664866
  have eq664910 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq664898
       have r₂ := eq27
       grind)
    | exact resolve eq664898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664898
  have eq664914 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649083 eq664910
    | exact resolve eq664910 eq649083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664910
  have eq667402 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq664914 eq27
    | exact resolve eq27 eq664914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667403 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq664914 eq51
    | exact resolve eq51 eq664914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq664914
  have eq668086 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq667403
       have r₂ := eq649053
       grind)
    | exact resolve eq667403 eq649053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667403
  have eq668112 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649053 eq668086
    | exact resolve eq668086 eq649053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649053 eq668086
  have eq670829 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq668112 eq49
    | exact resolve eq49 eq668112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq670872 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq668112 eq650128
    | exact resolve eq650128 eq668112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650128 eq668112
  have eq670923 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq670872
  have eq670937 : x = (M.op x y) := by
    first
    | (have r₁ := eq670923
       have r₂ := eq667402
       grind)
    | exact resolve eq670923 eq667402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667402 eq670923
  have eq670945 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq670829
    | exact resolve eq670829 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq670829
  have eq670954 : x = (k x x) := by
    first
    | (have r₁ := eq670945
       have r₂ := eq649961
       grind)
    | exact resolve eq670945 eq649961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649961 eq670945
  have eq670958 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq670937 eq20
    | exact resolve eq20 eq670937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq670937
  have eq671561 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq670958
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq670958
    | exact resolve eq670958 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670958
  have eq672817 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16568 x x
       have i₂ := eq670954
       grind)
    | exact superpose eq670954 eq16568
    | (have j0 := eq16568 x x
       grind)
    | exact resolve eq16568 eq670954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16568 eq670954
  have eq672818 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq672817
  have eq672828 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq672818
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq672818
    | exact resolve eq672818 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq672818
  have eq672873 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq649083 eq672828
    | exact resolve eq672828 eq649083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649083 eq672828
  have eq672916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq671561 eq672873
    | exact resolve eq672873 eq671561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671561 eq672873
  have eq672957 : False := by grind
  exact eq672957

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq396 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq422 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq423 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq422 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq427 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq423 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq423 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq423 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq435 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq427
    | (have j0 := eq427 X0 X1
       grind)
    | exact resolve eq427 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq436 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq441 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq436 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq436
    | exact resolve eq436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq436 x y
       grind)
    | exact superpose eq436 eq16
    | exact resolve eq16 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq565 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq441 X0 (τ X1)
       grind)
    | exact superpose eq441 eq17
    | exact resolve eq17 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq441
  have eq585 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq565
    | exact resolve eq565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq594 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq585
    | exact resolve eq585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq606 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq452
       have i₂ := eq594 x y
       grind)
    | exact superpose eq594 eq452
    | exact resolve eq452 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq594
  have eq607 : False := by grind
  exact eq607
