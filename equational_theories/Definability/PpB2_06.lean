import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq93 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq107 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq251 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq58 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 y x
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq690 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X0 X0) X0 X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 y x X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X2 (M.op X0 X1) X1
       have i₂ := eq58 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq789 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78
  have eq882 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq789 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq789
    | (have j0 := eq789 X0 x
       grind)
    | exact resolve eq789 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq4225 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X0 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq704
    | exact resolve eq704 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4278 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4225 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4225
    | (have j0 := eq4225 y x
       grind)
    | exact resolve eq4225 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4663 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq700 (M.op y X0) X0
       have i₂ := eq58 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq58 eq700
    | exact resolve eq700 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq4874 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq707 X0 X0 X2 X3 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq707
    | exact resolve eq707 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq5612 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq29 eq358
    | exact resolve eq358 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq5654 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq40 eq5612
    | (have j0 := eq5612 X0
       grind)
    | exact resolve eq5612 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5612
  have eq5822 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq882 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq882
    | (have j0 := eq882 y
       grind)
    | exact resolve eq882 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq5846 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5822
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq5822
    | exact resolve eq5822 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq5822
  have eq5866 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5846
    | exact resolve eq5846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5846
  have eq5879 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5866
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq5866
    | exact resolve eq5866 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq5866
  have eq7607 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq690
    | exact resolve eq690 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq9362 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq706 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq56 (M.op X1 X2)
       grind)
    | exact superpose eq56 eq706
    | exact resolve eq706 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq17232 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq704 X1 X0 X1
       grind)
    | exact superpose eq704 eq257
    | exact resolve eq257 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq24305 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4874 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq4874
    | exact resolve eq4874 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874
  have eq24523 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24305 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq24305
    | exact resolve eq24305 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25046 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq7607 X1 X0
       grind)
    | exact superpose eq7607 eq14
    | exact resolve eq14 eq7607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33674 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq251
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq251
    | exact resolve eq251 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq251
  have eq35852 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq24523 X0 y
       have i₂ := eq4663 X0
       grind)
    | exact superpose eq4663 eq24523
    | exact resolve eq24523 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq35856 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7607 X0 X1
       have i₂ := eq24523 X0 X1
       grind)
    | exact superpose eq24523 eq7607
    | exact resolve eq7607 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38450 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq729 X0 X1 X2
       have i₂ := eq24523 X1 X0
       grind)
    | exact superpose eq24523 eq729
    | exact resolve eq729 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq38809 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38450 X0 (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq7607 X0 X1
       grind)
    | exact superpose eq7607 eq38450
    | exact resolve eq38450 eq7607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7607
  have eq38826 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38450 (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq704 X0 X1 X2
       grind)
    | exact superpose eq704 eq38450
    | exact resolve eq38450 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq39207 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35856 X2 X1
       have i₂ := eq38450 X1 X2 X0
       grind)
    | (have i₁ := eq35856 (M.op X2 X0) X0
       have i₂ := eq38450 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq38450 eq35856
    | exact resolve eq35856 eq38450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39529 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38826 X0 X1 X2 X3
       have i₂ := eq256 (M.op X0 X1)
       grind)
    | exact superpose eq256 eq38826
    | exact resolve eq38826 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38826
  have eq39544 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38809 X0 X1 X2
       have i₂ := eq256 (M.op X0 X1)
       grind)
    | exact superpose eq256 eq38809
    | exact resolve eq38809 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq38809
  have eq39726 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39529 X0 X1 X2 X3
       have i₂ := eq24523 X1 X0
       grind)
    | exact superpose eq24523 eq39529
    | exact resolve eq39529 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39529
  have eq39730 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39544 X0 X1 X2
       have i₂ := eq24523 X1 X0
       grind)
    | exact superpose eq24523 eq39544
    | exact resolve eq39544 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39544
  have eq45037 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5879 eq56
    | exact resolve eq56 eq5879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45063 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5879 eq58
    | exact resolve eq58 eq5879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq45108 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45063
       have i₂ := eq24523 sF2 sF3
       grind)
    | exact superpose eq24523 eq45063
    | exact resolve eq45063 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45063
  have eq52678 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9362 X0 X1 X2 X3
       have i₂ := eq24523 X1 X0
       grind)
    | exact superpose eq24523 eq9362
    | exact resolve eq9362 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9362 eq24523
  have eq53356 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52678 X0 X1 X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq52678
    | exact resolve eq52678 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52678
  have eq54824 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53356 X1 X2
       have i₂ := eq38450 X1 X2 X0
       grind)
    | (have i₁ := eq53356 X0 (M.op X2 X0)
       have i₂ := eq38450 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq38450 eq53356
    | exact resolve eq53356 eq38450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38450 eq53356
  have eq113584 : y = (M.op x (M.op y x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq35852 eq33674
    | exact resolve eq33674 eq35852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33674 eq35852
  have eq129625 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq45108 eq35856
    | exact resolve eq35856 eq45108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129737 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq129625
    | exact resolve eq129625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129625
  have eq130324 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq129737 eq105
    | exact resolve eq105 eq129737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq129737
  have eq136247 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq35856 x y
       have i₂ := eq113584
       grind)
    | exact superpose eq113584 eq35856
    | exact resolve eq35856 eq113584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35856
  have eq136360 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq136247
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq136247
    | exact resolve eq136247 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136247
  have eq136400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq136360 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq136360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136360
  have eq136401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq136400
    | exact resolve eq136400 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136400
  have eq136417 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq136401
       have r₂ := eq28
       grind)
    | exact resolve eq136401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136401
  have eq137315 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq136417 eq56
    | exact resolve eq56 eq136417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137378 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (σ x))) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq136417 eq25046
    | exact resolve eq25046 eq136417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136417
  have eq137421 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq137378 x
       have i₂ := eq39726 sF3 sF2 x sF3
       grind)
    | exact superpose eq39726 eq137378
    | exact resolve eq137378 eq39726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137378
  have eq139819 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq137315 eq17232
    | exact resolve eq17232 eq137315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137315
  have eq149511 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq139819 eq137421
    | exact resolve eq137421 eq139819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137421 eq139819
  have eq149598 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq149511
  have eq149619 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq149598
       have i₂ := eq56 sF2
       grind)
    | exact superpose eq56 eq149598
    | exact resolve eq149598 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149598
  have eq149620 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq149619
  have eq149722 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (M.op x y) (M.op x X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54824 y x X0
       have i₂ := eq149620
       grind)
    | exact superpose eq149620 eq54824
    | exact resolve eq54824 eq149620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54824 eq149620
  have eq160752 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5654 y
       have i₂ := eq130324
       grind)
    | exact superpose eq130324 eq5654
    | (have j0 := eq5654 y
       grind)
    | exact resolve eq5654 eq130324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654 eq130324
  have eq161075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq160752
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq160752
    | exact resolve eq160752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160752
  have eq161102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq161075
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq161075
    | exact resolve eq161075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161075
  have eq161115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq161102
    | exact resolve eq161102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161102
  have eq161121 : (M.op y x) = (M.op y y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq161115
       have r₂ := eq28
       grind)
    | exact resolve eq161115 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161115
  have eq164892 : y = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq149722 (M.op y x)
       have i₂ := eq113584
       grind)
    | exact superpose eq113584 eq149722
    | exact resolve eq149722 eq113584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149722
  have eq165034 : y = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq164892
  have eq165078 : y = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4278 eq165034
    | exact resolve eq165034 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq165034
  have eq171289 : y = (M.op y (M.op y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq161121
       grind)
    | exact superpose eq161121 eq56
    | exact resolve eq56 eq161121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171355 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y x)) (M.op y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq25046 y y x
       have i₂ := eq161121
       grind)
    | exact superpose eq161121 eq25046
    | exact resolve eq25046 eq161121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046 eq161121
  have eq171402 : y = (M.op x (M.op y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq171355 x
       have i₂ := eq39726 y x x y
       grind)
    | exact superpose eq39726 eq171355
    | exact resolve eq171355 eq39726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39726 eq171355
  have eq171504 : (M.op x x) = (M.op y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17232 y x y
       have i₂ := eq171289
       grind)
    | exact superpose eq171289 eq17232
    | exact resolve eq17232 eq171289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17232 eq171289
  have eq173105 : y = (M.op x (M.op x x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq171402
       have i₂ := eq171504
       grind)
    | exact superpose eq171504 eq171402
    | exact resolve eq171402 eq171504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171402 eq171504
  have eq173206 : y = (M.op x (M.op x x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq173105
  have eq173229 : x = y ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq173206
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq173206
    | exact resolve eq173206 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173206
  have eq173230 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq173229
  have eq173900 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173230 eq45037
    | exact resolve eq45037 eq173230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45037
  have eq173937 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq173230 eq58
    | exact resolve eq58 eq173230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq173230
  have eq173996 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq173900
  have eq174114 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq173937 eq39207
    | exact resolve eq39207 eq173937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39207 eq173937
  have eq174155 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq174114 X0
       have i₂ := eq39730 (M.op X0 sF4) sF2 sF2
       grind)
    | exact superpose eq39730 eq174114
    | exact resolve eq174114 eq39730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39730 eq174114
  have eq216006 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq24305 x (M.op y y)
       have i₂ := eq165078
       grind)
    | exact superpose eq165078 eq24305
    | exact resolve eq24305 eq165078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24305 eq165078
  have eq236590 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq113584
       have i₂ := eq216006
       grind)
    | exact superpose eq216006 eq113584
    | exact resolve eq113584 eq216006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113584 eq216006
  have eq236709 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq236590
  have eq236729 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq236709
       have i₂ := eq56 x
       grind)
    | exact superpose eq56 eq236709
    | exact resolve eq236709 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq236709
  have eq236730 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq236729
  have eq237451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq236730 eq173996
    | exact resolve eq173996 eq236730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173996
  have eq237463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq237451
  have eq237477 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq237463
       have r₂ := eq28
       grind)
    | exact resolve eq237463 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237463
  have eq237624 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq237477 eq174155
    | exact resolve eq174155 eq237477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174155 eq237477
  have eq237693 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq237624
  have eq240337 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237693 eq45108
    | exact resolve eq45108 eq237693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45108 eq237693
  have eq240465 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq240337
  have eq240565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq240465 eq236730
    | exact resolve eq236730 eq240465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236730 eq240465
  have eq240577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq240565
  have eq240591 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq240577
       have r₂ := eq28
       grind)
    | exact resolve eq240577 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240577
  have eq240598 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq240591 eq30
    | exact resolve eq30 eq240591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq240591
  have eq240897 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq240598
    | exact resolve eq240598 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq240598
  have eq240898 : x = y := by grind
  clear eq240897
  have eq240926 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq240898
       grind)
    | exact superpose eq240898 eq19
    | exact resolve eq19 eq240898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq240927 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq240898
       grind)
    | exact superpose eq240898 eq25
    | exact resolve eq25 eq240898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq240898
  have eq241364 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq240927
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq240927
    | exact resolve eq240927 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq240927
  have eq241406 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq241364 eq27
    | exact resolve eq27 eq241364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq241364
  have eq242113 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq241406 eq75
    | exact resolve eq75 eq241406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq241406
  have eq242357 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq242113
       have i₂ := eq240926
       grind)
    | exact superpose eq240926 eq242113
    | exact resolve eq242113 eq240926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240926 eq242113
  have eq242442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq242357 eq15
    | exact resolve eq15 eq242357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242357
  have eq242863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq242442
    | exact resolve eq242442 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq242442
  have eq243002 : False := by grind
  exact eq243002

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq89
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq114 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq111
  have eq115 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq114
  have eq165 : (σ (k (M.op (M.op x y) (M.op x y)) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq115 eq40
    | exact resolve eq40 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq249 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq285 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq274
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq286 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq285
  have eq354 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq400 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X0 X0) X0 X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 y x X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq519 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq628 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75
  have eq666 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq16
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq752 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq628 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq628
    | (have j0 := eq628 X0 x
       grind)
    | exact resolve eq628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq931 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq253 (τ X0)
       have i₂ := eq666 X0
       grind)
    | exact superpose eq666 eq253
    | exact resolve eq253 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq666
  have eq2526 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 (M.op X0 X0) X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq402
    | exact resolve eq402 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4652 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq517 x X1 X0
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq517
    | exact resolve eq517 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq4671 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq4652 sF0 sF0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq4652
    | exact resolve eq4652 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4652
  have eq4723 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 sF2 X1 x
       have i₂ := eq58 sF2 sF2
       grind)
    | exact superpose eq58 eq519
    | exact resolve eq519 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq4848 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq4723 sF4 sF4
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq4723
    | exact resolve eq4723 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4907 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq508 (M.op y X0) X0
       have i₂ := eq58 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq58 eq508
    | exact resolve eq508 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq4959 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq510 (M.op sF3 x) x
       have i₂ := eq58 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq58 eq510
    | exact resolve eq510 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq5069 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq515 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq515
    | exact resolve eq515 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5136 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq515 X0 X0 X2 X3 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq515
    | exact resolve eq515 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq5790 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq91 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq6256 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq354 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq354
    | exact resolve eq354 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq6320 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6256 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq6256
    | (have j0 := eq6256 X0 X1
       grind)
    | exact resolve eq6256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq6362 : (σ (k (M.op (M.op x y) (M.op x y)) x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq115 eq752
    | exact resolve eq752 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq6481 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq165 eq6362
    | exact resolve eq6362 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq6362
  have eq6497 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6481
       have i₂ := eq58 sF0 sF0
       grind)
    | exact superpose eq58 eq6481
    | exact resolve eq6481 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6481
  have eq6509 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq6497
    | exact resolve eq6497 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6497
  have eq8937 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq58 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq58 eq498
    | exact resolve eq498 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq10257 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq514 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq56 (M.op X1 X2)
       grind)
    | exact superpose eq56 eq514
    | exact resolve eq514 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq514
  have eq17070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq17070
    | exact resolve eq17070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17070
  have eq17082 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq17071
       have r₂ := eq28
       grind)
    | exact resolve eq17071 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17071
  have eq17086 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq17082
    | exact resolve eq17082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17082
  have eq17089 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17086 eq249
    | exact resolve eq249 eq17086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq17118 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17086 eq931
    | exact resolve eq931 eq17086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq17149 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq17118
    | exact resolve eq17118 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17118
  have eq17159 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17089 eq54
    | exact resolve eq54 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq18311 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17149 eq58
    | exact resolve eq58 eq17149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17149
  have eq38019 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17086 eq5069
    | (have j0 := eq5069 (σ y) X0 (σ x)
       grind)
    | exact resolve eq5069 eq17086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq38166 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17089 eq38019
    | exact resolve eq38019 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17089 eq38019
  have eq38219 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38166
  have eq38271 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (k (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38219 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq38219 X0
       grind)
    | exact resolve eq12 eq38219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38219
  have eq38312 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38271 X0
       grind)
    | (have r₁ := eq38271 X0
       have r₂ := eq17086
       grind)
    | exact resolve eq38271 eq17086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086 eq38271
  have eq51412 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op y X0) (M.op y X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq18311 eq10257
    | exact resolve eq10257 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10257 eq18311
  have eq51936 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op y X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51412 X0
       have i₂ := eq4907 X0
       grind)
    | exact superpose eq4907 eq51412
    | exact resolve eq51412 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51412
  have eq77638 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51936 eq5136
    | exact resolve eq5136 eq51936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5136 eq51936
  have eq203121 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17159 eq38312
    | exact resolve eq38312 eq17159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17159 eq38312
  have eq203197 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq203121
  have eq203305 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq203197 eq100
    | exact resolve eq100 eq203197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203306 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq203197 eq103
    | exact resolve eq103 eq203197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq203197
  have eq203330 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq203306
  have eq203343 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq203305
    | exact resolve eq203305 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203305
  have eq203353 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq203330
       grind)
    | exact superpose eq203330 eq94
    | exact resolve eq94 eq203330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203383 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) X1)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq400 y X0 X1
       have i₂ := eq203330
       grind)
    | exact superpose eq203330 eq400
    | exact resolve eq400 eq203330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq203384 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq402 y x
       have i₂ := eq203330
       grind)
    | exact superpose eq203330 eq402
    | exact resolve eq402 eq203330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203330
  have eq203464 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq203384 x
       have i₂ := eq2526 sF0 x
       grind)
    | exact superpose eq2526 eq203384
    | exact resolve eq203384 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203384
  have eq203465 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) X1)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq21 eq203383
    | (have j0 := eq203383 X0 X1
       grind)
    | exact resolve eq203383 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203383
  have eq203482 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq203353
    | exact resolve eq203353 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203353
  have eq203496 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq115 eq203464
    | exact resolve eq203464 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203464
  have eq203497 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) X1)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq203465 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq203465
    | (have j0 := eq203465 X0 X1
       grind)
    | exact resolve eq203465 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203465
  have eq203506 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq203496
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq203496
    | exact resolve eq203496 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203496
  have eq208211 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq402 y x
       have i₂ := eq203343
       grind)
    | exact superpose eq203343 eq402
    | exact resolve eq402 eq203343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq203343
  have eq208292 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq208211 x
       have i₂ := eq2526 sF0 x
       grind)
    | exact superpose eq2526 eq208211
    | exact resolve eq208211 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526 eq208211
  have eq208323 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq115 eq208292
    | exact resolve eq208292 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq208292
  have eq208333 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq208323
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq208323
    | exact resolve eq208323 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208323
  have eq229026 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq208333 eq6509
    | exact resolve eq6509 eq208333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208333
  have eq229027 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq203506 eq6509
    | exact resolve eq6509 eq203506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509 eq203506
  have eq229033 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq229027
  have eq229034 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq229026
  have eq229039 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq229033
    | exact resolve eq229033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229033
  have eq229040 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq27 eq229034
    | exact resolve eq229034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229034
  have eq229041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq229039
    | exact resolve eq229039 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229039
  have eq229042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq27 eq229040
    | exact resolve eq229040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229040
  have eq229043 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq229041
       have r₂ := eq28
       grind)
    | exact resolve eq229041 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229041
  have eq229044 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq229042
       have r₂ := eq28
       grind)
    | exact resolve eq229042 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229042
  have eq229217 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq229044 eq100
    | exact resolve eq100 eq229044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq229044
  have eq229307 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6320 x y
       have i₂ := eq229217
       grind)
    | exact superpose eq229217 eq6320
    | (have j0 := eq6320 x y
       grind)
    | exact resolve eq6320 eq229217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320 eq229217
  have eq229309 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq229307
  have eq229315 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have j1 := eq12 (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq229309
       have r₂ := eq12 y x
       grind)
    | exact resolve eq229309 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229309
  have eq229344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq229315
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq229315
    | exact resolve eq229315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229315
  have eq229365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq229344
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq229344
    | exact resolve eq229344 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229344
  have eq229377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq21 eq229365
    | exact resolve eq229365 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229365
  have eq229385 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq229377
       have r₂ := eq28
       grind)
    | exact resolve eq229377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229377
  have eq229398 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq229385
       grind)
    | exact superpose eq229385 eq88
    | exact resolve eq88 eq229385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq229414 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5790 x
       have i₂ := eq229385
       grind)
    | exact superpose eq229385 eq5790
    | (have j0 := eq5790 x
       grind)
    | exact resolve eq5790 eq229385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5790 eq229385
  have eq229441 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq229414
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq229414
    | exact resolve eq229414 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229414
  have eq229456 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq229398
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq229398
    | exact resolve eq229398 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229398
  have eq229467 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq229441
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq229441
    | exact resolve eq229441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229441
  have eq229479 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq229467
    | exact resolve eq229467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229467
  have eq229488 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq229479
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq229479
    | exact resolve eq229479 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229479
  have eq229489 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq229488
  have eq229629 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq229456 eq229043
    | exact resolve eq229043 eq229456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229043 eq229456
  have eq229645 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq229629
  have eq229692 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq229645 eq4848
    | exact resolve eq4848 eq229645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848
  have eq262546 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq229692 eq4959
    | exact resolve eq4959 eq229692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4959 eq229692
  have eq262637 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq262546
       have i₂ := eq58 sF2 sF2
       grind)
    | exact superpose eq58 eq262546
    | exact resolve eq262546 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262546
  have eq302494 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq229645 eq262637
    | exact resolve eq262637 eq229645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229645 eq262637
  have eq302587 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq302494
  have eq314546 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq302587 eq203497
    | exact resolve eq203497 eq302587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203497 eq302587
  have eq314625 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq314546 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314546
  have eq326866 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq314625 eq8937
    | exact resolve eq8937 eq314625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937 eq314625
  have eq326942 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq326866
    | exact resolve eq326866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326866
  have eq327672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq326942 eq203482
    | exact resolve eq203482 eq326942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203482 eq326942
  have eq327880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq327672
  have eq327964 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq327880
       have r₂ := eq28
       grind)
    | exact resolve eq327880 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327880
  have eq327973 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq327964 eq30
    | exact resolve eq30 eq327964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328158 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq327973
    | exact resolve eq327973 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327973
  have eq328159 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq328158
  have eq328180 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq328159 eq30
    | exact resolve eq30 eq328159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328159
  have eq329183 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq328180
    | exact resolve eq328180 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq328180
  have eq329371 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq329183 eq4671
    | exact resolve eq4671 eq329183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq333974 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq4907 x
       have i₂ := eq329371
       grind)
    | exact superpose eq329371 eq4907
    | exact resolve eq4907 eq329371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907 eq329371
  have eq334063 : x = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq333974
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq333974
    | exact resolve eq333974 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq333974
  have eq338985 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq329183 eq334063
    | exact resolve eq334063 eq329183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329183 eq334063
  have eq339068 : x = (M.op y (M.op x x)) ∨ x = y := by grind
  clear eq338985
  have eq347296 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq77638 (M.op x x)
       have i₂ := eq339068
       grind)
    | exact superpose eq339068 eq77638
    | exact resolve eq77638 eq339068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77638 eq339068
  have eq347381 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq347296
  have eq347394 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq347381
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq347381
    | exact resolve eq347381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347381
  have eq347395 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq347394
  have eq359921 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq347395
       grind)
    | exact superpose eq347395 eq94
    | exact resolve eq94 eq347395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq347395
  have eq360107 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq359921
    | exact resolve eq359921 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359921
  have eq361589 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq360107 eq229489
    | exact resolve eq229489 eq360107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229489 eq360107
  have eq361809 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq361589
  have eq361913 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq361809
       have r₂ := eq327964
       grind)
    | exact resolve eq361809 eq327964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327964 eq361809
  have eq361937 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq361913
       have r₂ := eq28
       grind)
    | exact resolve eq361913 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361913
  have eq361945 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq361937 eq30
    | exact resolve eq30 eq361937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq361937
  have eq362196 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq361945
    | exact resolve eq361945 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq361945
  have eq362197 : x = y := by grind
  clear eq362196
  have eq362216 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq362197
       grind)
    | exact superpose eq362197 eq19
    | exact resolve eq19 eq362197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq362217 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq362197
       grind)
    | exact superpose eq362197 eq25
    | exact resolve eq25 eq362197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq362197
  have eq362554 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq362217
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq362217
    | exact resolve eq362217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq362217
  have eq362586 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq362554 eq27
    | exact resolve eq27 eq362554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq362554
  have eq363094 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq362586 eq72
    | exact resolve eq72 eq362586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq362586
  have eq363276 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq363094
       have i₂ := eq362216
       grind)
    | exact superpose eq362216 eq363094
    | exact resolve eq363094 eq362216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362216 eq363094
  have eq363370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq363276 eq15
    | exact resolve eq15 eq363276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363276
  have eq363861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq363370
    | exact resolve eq363370 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq363370
  have eq363998 : False := by grind
  exact eq363998

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq487 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X0 X0) X0 X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq7564 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq487
    | exact resolve eq487 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq21100 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq7564 X1 X0
       grind)
    | exact superpose eq7564 eq14
    | exact resolve eq14 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564
  have eq29096 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq58 y y
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq58
    | exact resolve eq58 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq29120 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq29096
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq29096
    | exact resolve eq29096 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq29096
  have eq29121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq29120
  have eq29180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29121 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq29121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29121
  have eq29181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq29180
    | exact resolve eq29180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29180
  have eq29192 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29181
       have r₂ := eq28
       grind)
    | exact resolve eq29181 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29181
  have eq29277 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29192 eq21100
    | exact resolve eq21100 eq29192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21100 eq29192
  have eq29279 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29277 x
       have i₂ := eq14 sF2 x sF2
       grind)
    | exact superpose eq14 eq29277
    | exact resolve eq29277 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29277
  have eq29280 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29279
  have eq29317 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29280 eq30
    | exact resolve eq30 eq29280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29280
  have eq29507 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq29317
    | exact resolve eq29317 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29317
  have eq29508 : x = y := by grind
  clear eq29507
  have eq29529 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29508
       grind)
    | exact superpose eq29508 eq19
    | exact resolve eq19 eq29508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29530 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29508
       grind)
    | exact superpose eq29508 eq25
    | exact resolve eq25 eq29508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29508
  have eq29723 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29530
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29530
    | exact resolve eq29530 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29530
  have eq29744 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29723 eq27
    | exact resolve eq27 eq29723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29723
  have eq30945 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29744 eq78
    | exact resolve eq78 eq29744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq29744
  have eq31036 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30945
       have i₂ := eq29529
       grind)
    | exact superpose eq29529 eq30945
    | exact resolve eq30945 eq29529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29529 eq30945
  have eq31069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31036 eq15
    | exact resolve eq15 eq31036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31036
  have eq31158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq31069
    | exact resolve eq31069 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31069
  have eq31192 : False := by grind
  exact eq31192

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
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
  have eq84 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq487 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X0 X0) X0 X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq7563 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq487
    | exact resolve eq487 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq21098 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq7563 X1 X0
       grind)
    | exact superpose eq7563 eq14
    | exact resolve eq14 eq7563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7563
  have eq29093 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq58 y y
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq58
    | exact resolve eq58 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq29117 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq29093
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq29093
    | exact resolve eq29093 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq29093
  have eq29118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq29117
  have eq29176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq29118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29118
  have eq29177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq29176
    | exact resolve eq29176 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29176
  have eq29188 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29177
       have r₂ := eq28
       grind)
    | exact resolve eq29177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29177
  have eq29273 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29188 eq21098
    | exact resolve eq21098 eq29188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21098 eq29188
  have eq29275 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29273 x
       have i₂ := eq14 sF2 x sF2
       grind)
    | exact superpose eq14 eq29273
    | exact resolve eq29273 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29273
  have eq29276 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29275
  have eq29313 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29276 eq30
    | exact resolve eq30 eq29276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29276
  have eq29503 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq29313
    | exact resolve eq29313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29313
  have eq29504 : x = y := by grind
  clear eq29503
  have eq29525 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29504
       grind)
    | exact superpose eq29504 eq19
    | exact resolve eq19 eq29504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29526 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29504
       grind)
    | exact superpose eq29504 eq25
    | exact resolve eq25 eq29504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29504
  have eq29719 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29526
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29526
    | exact resolve eq29526 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29526
  have eq29740 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29719 eq27
    | exact resolve eq27 eq29719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29719
  have eq30940 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29740 eq71
    | exact resolve eq71 eq29740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq29740
  have eq31031 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30940
       have i₂ := eq29525
       grind)
    | exact superpose eq29525 eq30940
    | exact resolve eq30940 eq29525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29525 eq30940
  have eq31064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31031 eq15
    | exact resolve eq15 eq31031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31031
  have eq31153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq31064
    | exact resolve eq31064 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31064
  have eq31187 : False := by grind
  exact eq31187

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq48 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq49 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq48
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq48
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq69
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq69
    | exact resolve eq69 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq72
    | exact resolve eq72 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq219 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ (k x (k (τ X0) X1))) = (k (σ x) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq37
    | exact resolve eq37 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq37
  have eq237 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq28 eq57
    | (have j0 := eq57 (σ y) (σ x)
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq309 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 X0) X0 X1 X2
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 y x X0 X1
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq54
    | (have j0 := eq54 y x X0 X1
       grind)
    | exact resolve eq54 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  have eq325 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq783 : ∀ X0 X1 : G, (k (σ x) (k X0 (σ X1))) = (σ (M.op x (k (τ X0) X1))) ∨ (k (τ X0) X1) = (M.op x x) ∨ x = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq11 x (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq223
    | (have j1 := eq11 x (k (τ X0) X1)
       grind)
    | exact resolve eq223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2893 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X0 X1
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq321
    | exact resolve eq321 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq2928 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq28 eq2893
    | (have j0 := eq2893 (σ y) (σ x)
       grind)
    | exact resolve eq2893 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4122 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq317 (M.op y X0) X0
       have i₂ := eq57 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq57 eq317
    | exact resolve eq317 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq4395 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq325 X0 X0 X2 X3 X1
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq325
    | exact resolve eq325 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq5151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq5151
    | exact resolve eq5151 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq5163 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq5152
       have r₂ := eq29
       grind)
    | exact resolve eq5152 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5152
  have eq5175 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5163 eq55
    | exact resolve eq55 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163
  have eq5207 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq5175
    | exact resolve eq5175 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5175
  have eq5224 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq240 x
       have i₂ := eq5207
       grind)
    | exact superpose eq5207 eq240
    | exact resolve eq240 eq5207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq5239 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5224
  have eq5419 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq48
    | exact resolve eq48 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq5239
  have eq5435 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5419
    | exact resolve eq5419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419
  have eq5653 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5435 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq5435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435
  have eq5654 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5653
  have eq5658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq5654
    | exact resolve eq5654 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq5659 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5658
  have eq5943 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1 (M.op X0 X0)
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq309
    | exact resolve eq309 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq6055 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5659 eq55
    | exact resolve eq55 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq6096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq6055
    | exact resolve eq6055 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6055
  have eq6097 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6096
  have eq6098 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6097 eq29
    | exact resolve eq29 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6107 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6097 eq2928
    | exact resolve eq2928 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq6118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq6107
    | exact resolve eq6107 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6107
  have eq6121 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6118 eq237
    | exact resolve eq237 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq6118
  have eq6157 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6097 eq6121
    | exact resolve eq6121 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6097 eq6121
  have eq6199 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6157
  have eq6425 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6199 eq240
    | exact resolve eq240 eq6199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199
  have eq6453 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6425
  have eq7053 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6453 eq73
    | exact resolve eq73 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq6453
  have eq7063 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7053
  have eq7072 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7063
       have r₂ := eq6098
       grind)
    | exact resolve eq7063 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq7390 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq7072
       grind)
    | exact superpose eq7072 eq55
    | exact resolve eq55 eq7072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq7072
  have eq7437 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7390
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq7390
    | exact resolve eq7390 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390
  have eq7439 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7437 eq31
    | exact resolve eq31 eq7437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7437
  have eq7524 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq7439
    | exact resolve eq7439 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439
  have eq7525 : x = (M.op x y) ∨ x = y := by grind
  clear eq7524
  have eq7550 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq7525 eq22
    | exact resolve eq22 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7643 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq7550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7550
    | exact resolve eq7550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7550
  have eq7723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq7643 eq6098
    | (have r₁ := eq6098
       have r₂ := eq7643
       grind)
    | exact resolve eq6098 eq7643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6098 eq7643
  have eq7732 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq7723
  have eq7733 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq7732
  have eq7807 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq7733 eq31
    | exact resolve eq31 eq7733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7733
  have eq7914 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq7807
    | exact resolve eq7807 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807
  have eq7992 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq7914 eq7525
    | exact resolve eq7525 eq7914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7525 eq7914
  have eq7993 : x = y := by grind
  clear eq7992
  have eq8190 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq7993
       grind)
    | exact superpose eq7993 eq20
    | exact resolve eq20 eq7993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq8191 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq7993
       grind)
    | exact superpose eq7993 eq26
    | exact resolve eq26 eq7993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8275 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8191
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8191
    | exact resolve eq8191 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8191
  have eq8299 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8275 eq28
    | exact resolve eq28 eq8275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8275
  have eq8444 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq8190
       grind)
    | exact superpose eq8190 eq14
    | exact resolve eq14 eq8190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8454 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq240 x
       have i₂ := eq8190
       grind)
    | exact superpose eq8190 eq240
    | exact resolve eq240 eq8190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9216 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq8299 eq57
    | exact resolve eq57 eq8299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10135 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9216 eq240
    | exact resolve eq240 eq9216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9216
  have eq12678 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8454 eq49
    | exact resolve eq49 eq8454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq8454
  have eq12696 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12678
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12678
    | exact resolve eq12678 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12678
  have eq12749 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12696 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq12696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12696
  have eq12750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8299 eq12749
    | exact resolve eq12749 eq8299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12749
  have eq12761 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12750
       have r₂ := eq29
       grind)
    | exact resolve eq12750 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12750
  have eq29085 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12761 eq2893
    | exact resolve eq2893 eq12761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2893
  have eq82012 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq4122 X0
       have i₂ := eq7993
       grind)
    | exact superpose eq7993 eq4122
    | exact resolve eq4122 eq7993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122 eq7993
  have eq86056 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq5943 X0 x
       have i₂ := eq82012 X0
       grind)
    | (have i₁ := eq5943 y x
       have i₂ := eq82012 y
       grind)
    | exact superpose eq82012 eq5943
    | exact resolve eq5943 eq82012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5943 eq82012
  have eq87467 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq86056 eq14
    | exact resolve eq14 eq86056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86056
  have eq88681 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4395 X0 (M.op x (M.op x (M.op X0 X1))) (M.op X0 X1) X1
       have i₂ := eq87467 (M.op X0 X1) x
       grind)
    | exact superpose eq87467 eq4395
    | exact resolve eq4395 eq87467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq226676 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29085 eq12761
    | exact resolve eq12761 eq29085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12761 eq29085
  have eq226785 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq226676
  have eq226912 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq226785 eq57
    | exact resolve eq57 eq226785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226785
  have eq227059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8299 eq226912
    | exact resolve eq226912 eq8299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226912
  have eq227083 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq227059
       have r₂ := eq29
       grind)
    | exact resolve eq227059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227059
  have eq227099 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq227083 eq30
    | exact resolve eq30 eq227083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq227083
  have eq227535 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq227099
    | exact resolve eq227099 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227099
  have eq227536 : x = (M.op x y) := by grind
  clear eq227535
  have eq227655 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq227536 eq22
    | exact resolve eq22 eq227536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq227748 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq227536 eq8444
    | exact resolve eq8444 eq227536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8444
  have eq228001 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq227655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq227655
    | exact resolve eq227655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227655
  have eq228251 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq228001 eq8299
    | exact resolve eq8299 eq228001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8299
  have eq228260 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq228001 eq10135
    | exact resolve eq10135 eq228001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10135
  have eq228567 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq228260
       have r₂ := eq29
       grind)
    | exact resolve eq228260 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228260
  have eq461456 : ∀ X0 X1 : G, (k (σ (M.op x y)) (k X0 (σ X1))) = (σ (M.op x (k (τ X0) X1))) ∨ (k (τ X0) X1) = (M.op x x) ∨ x = (k (τ X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq228001 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq228001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq461457 : ∀ X0 X1 : G, (M.op x y) = (k (τ X0) X1) ∨ (k (σ (M.op x y)) (k X0 (σ X1))) = (σ (M.op x (k (τ X0) X1))) ∨ x = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq461456 X0 X1
       have i₂ := eq8190
       grind)
    | exact superpose eq8190 eq461456
    | (have j0 := eq461456 X0 X1
       grind)
    | exact resolve eq461456 eq8190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461456
  have eq461458 : ∀ X0 X1 : G, x = (k (τ X0) X1) ∨ (k (σ (M.op x y)) (k X0 (σ X1))) = (σ (M.op x (k (τ X0) X1))) ∨ x = (k (τ X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq227536 eq461457
    | (have j0 := eq461457 X0 X1
       grind)
    | exact resolve eq461457 eq227536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461457
  have eq461459 : ∀ X0 X1 : G, (k (σ (M.op x y)) (k X0 (σ X1))) = (σ (M.op x (k (τ X0) X1))) ∨ x = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq461458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461458
  have eq461534 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (σ (M.op x y)) (k X0 (σ (τ X0)))) ∨ (τ X0) = x := by
    intro X0
    grind
  clear eq461459
  have eq461697 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (σ (M.op x y)) (k X0 X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq461534 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq461534
    | (have j0 := eq461534 X0
       grind)
    | exact resolve eq461534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461534
  have eq461797 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = x := by
    intro X0
    grind
  clear eq461697
  have eq462506 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 (M.op x (τ X0))
       have i₂ := eq461797 X0
       grind)
    | exact superpose eq461797 eq16
    | (have j1 := eq461797 X0
       grind)
    | exact resolve eq16 eq461797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461797
  have eq465514 : ∀ X0 : G, (τ X0) = (M.op (τ (k (σ (M.op x y)) X0)) (M.op (τ X0) (τ X0))) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0) x
       have i₂ := eq462506 X0
       grind)
    | exact superpose eq462506 eq57
    | (have j1 := eq462506 X0
       grind)
    | exact resolve eq57 eq462506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq462506
  have eq3388319 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (σ (M.op x y))) (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (τ (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq465514 (M.op sF1 sF1)
       have i₂ := eq240 sF1
       grind)
    | exact superpose eq240 eq465514
    | (have j0 := eq465514 (M.op (σ (M.op x y)) (σ (M.op x y)))
       have j1 := eq240 (σ (M.op x y))
       grind)
    | exact resolve eq465514 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq465514
  have eq3389190 : (τ (M.op (σ x) (σ y))) = (M.op (τ (σ (M.op x y))) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq228251 eq3388319
    | exact resolve eq3388319 eq228251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388319
  have eq3389371 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq32 eq3389190
    | exact resolve eq3389190 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3389190
  have eq3389460 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq227536 eq3389371
    | exact resolve eq3389371 eq227536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389371
  have eq3389527 : x = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq228251 eq3389460
    | exact resolve eq3389460 eq228251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389460
  have eq3389581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq228251 eq3389527
    | exact resolve eq3389527 eq228251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228251 eq3389527
  have eq3389631 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3389581
       have r₂ := eq29
       grind)
    | exact resolve eq3389581 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389581
  have eq3404923 : (M.op x x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3389631 eq88681
    | exact resolve eq88681 eq3389631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88681 eq3389631
  have eq3405327 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3404923
       have i₂ := eq8190
       grind)
    | exact superpose eq8190 eq3404923
    | exact resolve eq3404923 eq8190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8190 eq3404923
  have eq3405534 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq227536 eq3405327
    | exact resolve eq3405327 eq227536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227536 eq3405327
  have eq3405680 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3405534 eq219
    | (have j0 := eq219 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq219 eq3405534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq3405534
  have eq3406105 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq3405680
  have eq3406273 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3406105
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3406105
    | exact resolve eq3406105 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406105
  have eq3406373 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq228001 eq3406273
    | exact resolve eq3406273 eq228001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406273
  have eq3406437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq228567 eq3406373
    | exact resolve eq3406373 eq228567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228567 eq3406373
  have eq3406494 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3406437
       have r₂ := eq29
       grind)
    | exact resolve eq3406437 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406437
  have eq3408024 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x (τ (M.op (σ x) (σ y))))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3406494 eq87467
    | exact resolve eq87467 eq3406494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87467 eq3406494
  have eq3409203 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3408024 x
       have i₂ := eq227748 x (τ sF4)
       grind)
    | exact superpose eq227748 eq3408024
    | exact resolve eq3408024 eq227748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227748 eq3408024
  have eq3409204 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq3409203
  have eq3416574 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3409204 eq15
    | exact resolve eq15 eq3409204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409204
  have eq3417190 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3416574
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3416574
    | exact resolve eq3416574 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3416574
  have eq3417372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq228001 eq3417190
    | exact resolve eq3417190 eq228001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228001 eq3417190
  have eq3417487 : False := by grind
  exact eq3417487

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq12342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq12342
    | exact resolve eq12342 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12342
  have eq12354 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq12343
       have r₂ := eq28
       grind)
    | exact resolve eq12343 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12343
  have eq12358 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq12354
    | exact resolve eq12354 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12354
  have eq12364 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12358 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12358
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12358
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12358
       grind)
    | exact resolve eq12 eq12358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12358
  have eq12384 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq12364
  have eq12388 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq12384
       have r₂ := eq27
       grind)
    | exact resolve eq12384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12384
  have eq12449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12388 eq106
    | exact resolve eq106 eq12388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq12388
  have eq12458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12449
  have eq12461 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12458
       have r₂ := eq28
       grind)
    | exact resolve eq12458 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12458
  have eq12467 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12461
       grind)
    | exact superpose eq12461 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12461
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12461
       grind)
    | exact resolve eq12 eq12461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12461
  have eq12487 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq12467
  have eq12491 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12487
       have r₂ := eq19
       grind)
    | exact resolve eq12487 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12487
  have eq12507 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq12491
       grind)
    | exact superpose eq12491 eq91
    | exact resolve eq91 eq12491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq12491
  have eq12523 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12507
    | exact resolve eq12507 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12507
  have eq12558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12523 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12558
  have eq12563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12559
    | exact resolve eq12559 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12559
  have eq12574 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12563
       have r₂ := eq28
       grind)
    | exact resolve eq12563 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12563
  have eq12578 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12574
    | exact resolve eq12574 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12574
  have eq12624 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12578 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12578
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12578
       grind)
    | exact resolve eq12 eq12578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12578
  have eq12644 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq12624
  have eq12648 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12644
       have r₂ := eq27
       grind)
    | exact resolve eq12644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12644
  have eq12664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12648 eq12523
    | exact resolve eq12523 eq12648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12523 eq12648
  have eq12667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12664
  have eq12672 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12667
       have r₂ := eq28
       grind)
    | exact resolve eq12667 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12667
  have eq12675 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12672 eq30
    | exact resolve eq30 eq12672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12672
  have eq12788 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12675
    | exact resolve eq12675 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12675
  have eq12789 : x = y := by grind
  clear eq12788
  have eq12808 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12789
       grind)
    | exact superpose eq12789 eq19
    | exact resolve eq19 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12809 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12789
       grind)
    | exact superpose eq12789 eq25
    | exact resolve eq25 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12789
  have eq12919 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12809
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12809
    | exact resolve eq12809 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12809
  have eq13272 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12919 eq27
    | exact resolve eq27 eq12919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12919
  have eq13539 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13272 eq77
    | exact resolve eq77 eq13272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq13272
  have eq13611 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13539
       have i₂ := eq12808
       grind)
    | exact superpose eq12808 eq13539
    | exact resolve eq13539 eq12808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12808 eq13539
  have eq13947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13611 eq15
    | exact resolve eq15 eq13611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13611
  have eq13996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13947
    | exact resolve eq13947 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13947
  have eq14005 : False := by grind
  exact eq14005

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq79 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq11505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq11505
    | exact resolve eq11505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11505
  have eq11517 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq11506
       have r₂ := eq28
       grind)
    | exact resolve eq11506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11506
  have eq11521 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq11517
    | exact resolve eq11517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11517
  have eq11677 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11521 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11521
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11521
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11521
       grind)
    | exact resolve eq12 eq11521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq11695 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq11677
  have eq11699 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq11695
       have r₂ := eq27
       grind)
    | exact resolve eq11695 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11695
  have eq11708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11699 eq75
    | exact resolve eq75 eq11699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq11699
  have eq11717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11708
  have eq11720 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11717
       have r₂ := eq28
       grind)
    | exact resolve eq11717 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11717
  have eq11961 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11720
       grind)
    | exact superpose eq11720 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11720
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11720
       grind)
    | exact resolve eq12 eq11720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11720
  have eq11979 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq11961
  have eq11983 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11979
       have r₂ := eq19
       grind)
    | exact resolve eq11979 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11979
  have eq11988 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq11983
       grind)
    | exact superpose eq11983 eq49
    | exact resolve eq49 eq11983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11983
  have eq12004 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11988
    | exact resolve eq11988 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11988
  have eq12092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12004 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12092
  have eq12097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12093
    | exact resolve eq12093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12093
  have eq12108 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12097
       have r₂ := eq28
       grind)
    | exact resolve eq12097 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097
  have eq12112 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12108
    | exact resolve eq12108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12108
  have eq12153 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12112 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12112
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12112
       grind)
    | exact resolve eq12 eq12112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq12171 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq12153
  have eq12175 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12171
       have r₂ := eq27
       grind)
    | exact resolve eq12171 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12171
  have eq12192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12175 eq12004
    | exact resolve eq12004 eq12175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12004 eq12175
  have eq12195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12192
  have eq12200 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12195
       have r₂ := eq28
       grind)
    | exact resolve eq12195 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq12217 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12200 eq30
    | exact resolve eq30 eq12200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12200
  have eq12326 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12217
    | exact resolve eq12217 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12217
  have eq12327 : x = y := by grind
  clear eq12326
  have eq12342 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12327
       grind)
    | exact superpose eq12327 eq19
    | exact resolve eq19 eq12327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12343 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12327
       grind)
    | exact superpose eq12327 eq25
    | exact resolve eq25 eq12327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12327
  have eq12453 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12343
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12343
    | exact resolve eq12343 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12343
  have eq12468 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12453 eq27
    | exact resolve eq27 eq12453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12453
  have eq12723 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12468 eq79
    | exact resolve eq79 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq12468
  have eq12793 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12723
       have i₂ := eq12342
       grind)
    | exact superpose eq12342 eq12723
    | exact resolve eq12723 eq12342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12342 eq12723
  have eq12802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12793 eq15
    | exact resolve eq15 eq12793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12793
  have eq12851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12802
    | exact resolve eq12802 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12802
  have eq12860 : False := by grind
  exact eq12860

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_y_x_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq69 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq69 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq69
    | exact resolve eq69 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq168 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq84 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq84
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq205 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : x ≠ (M.op x y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq16
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq205 (M.op X0 X0)
       have i₂ := eq211 X0 X0
       grind)
    | exact superpose eq211 eq205
    | exact resolve eq205 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq811 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq811
       grind)
    | exact superpose eq811 eq41
    | exact resolve eq41 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq853 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq852
    | exact resolve eq852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq855 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq853
    | exact resolve eq853 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq855 eq813
    | exact resolve eq813 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq863
       have r₂ := eq27
       grind)
    | exact resolve eq863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq874 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq870 eq207
    | (have r₁ := eq207
       have r₂ := eq870
       grind)
    | exact resolve eq207 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq878 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq870 eq27
    | exact resolve eq27 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq879 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq874
  have eq880 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq879
  have eq883 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq880 eq855
    | exact resolve eq855 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq887 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq880 eq168
    | exact resolve eq168 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq880
  have eq889 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq883
  have eq892 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq887
    | exact resolve eq887 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq895 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq889
       have r₂ := eq878
       grind)
    | exact resolve eq889 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq889
  have eq897 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq892
       have r₂ := eq206
       grind)
    | exact resolve eq892 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq892
  have eq900 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq895 eq897
    | exact resolve eq897 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq905 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq895 eq31
    | exact resolve eq31 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq931 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq905
    | exact resolve eq905 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq932 : x = (M.op x y) ∨ x = y := by grind
  clear eq931
  have eq936 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq932
       grind)
    | exact superpose eq932 eq22
    | exact resolve eq22 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq944 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq936
    | exact resolve eq936 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq995 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq900 eq41
    | exact resolve eq41 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq900
  have eq996 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq995
    | exact resolve eq995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq998 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq944 eq996
    | exact resolve eq996 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq998 eq813
    | exact resolve eq813 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq998
  have eq1017 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1013
  have eq1028 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1017 eq27
    | exact resolve eq27 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1035 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1028
       have r₂ := eq944
       grind)
    | exact resolve eq1028 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq1028
  have eq1037 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1035 eq31
    | exact resolve eq31 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1035
  have eq1062 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1037
    | exact resolve eq1037 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1063 : x = y := by grind
  clear eq1062
  have eq1074 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq18
    | exact resolve eq18 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1075 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq24
    | exact resolve eq24 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1063
  have eq1082 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1075
    | exact resolve eq1075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1082 eq26
    | exact resolve eq26 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1082
  have eq1115 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq228 x
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq228
    | exact resolve eq228 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq211 x X0
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq211
    | exact resolve eq211 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1124 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1083 eq228
    | exact resolve eq228 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq1128 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1083 eq211
    | exact resolve eq211 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1083
  have eq1133 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1115 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq1115
       grind)
    | exact resolve eq12 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1135 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq1133
  have eq1159 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1124 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq1124
       grind)
    | exact resolve eq12 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1161 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1159
  have eq1182 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1128 eq16
    | exact resolve eq16 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1412 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1135 eq40
    | exact resolve eq40 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1135
  have eq1418 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1412
    | exact resolve eq1412 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1434 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1161 eq156
    | exact resolve eq156 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq1446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1418 eq837
    | (have j0 := eq837 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq837 (σ (M.op x y)) (σ x)
       have r₂ := eq1418
       grind)
    | exact resolve eq837 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1447 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1446
  have eq1699 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1434 eq837
    | (have j0 := eq837 (τ (M.op (σ x) (σ y))) x
       grind)
    | (have r₁ := eq837 (τ (M.op (σ x) (σ y))) x
       have r₂ := eq1434
       grind)
    | exact resolve eq837 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq1434
  have eq1700 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1699
  have eq1721 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1447 eq1182
    | exact resolve eq1182 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1447 eq1721
    | exact resolve eq1721 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447 eq1721
  have eq1733 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1730
       have r₂ := eq27
       grind)
    | exact resolve eq1730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1735 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1733 eq28
    | exact resolve eq28 eq1733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1733
  have eq1761 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1735
    | exact resolve eq1735 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1735
  have eq1762 : x = (M.op x y) := by grind
  clear eq1761
  have eq2008 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq22
    | exact resolve eq22 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2029 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2008 eq20
    | exact resolve eq20 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq3462 : x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1700 eq1116
    | exact resolve eq1116 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq1700
  have eq3476 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3462
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq3462
    | exact resolve eq3462 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3481 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3476
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq3476
    | exact resolve eq3476 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762 eq3476
  have eq3493 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3481 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481
  have eq3503 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3493
  have eq3505 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (τ (M.op (σ x) (σ y))) (M.op x y)
       grind)
    | (have r₁ := eq3503
       have r₂ := eq13 (M.op x y) (k (τ (M.op (σ x) (σ y))) (M.op x y))
       grind)
    | (have r₁ := eq3503
       have r₂ := eq13 (k (τ (M.op (σ x) (σ y))) (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq3503
       have r₂ := eq13 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq3503 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq3511 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3505 eq35
    | exact resolve eq35 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3505
  have eq3520 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3511
    | exact resolve eq3511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3511
  have eq3523 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2029 eq3520
    | exact resolve eq3520 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520
  have eq3526 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have j1 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq3523
       have r₂ := eq13 (σ x) (k (M.op (σ x) (σ y)) (σ x))
       grind)
    | (have r₁ := eq3523
       have r₂ := eq13 (k (M.op (σ x) (σ y)) (σ x)) (σ x)
       grind)
    | (have r₁ := eq3523
       have r₂ := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3523 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq3532 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3526 eq1161
    | exact resolve eq1161 eq3526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq3526
  have eq3537 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3532
  have eq3547 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3537 eq27
    | exact resolve eq27 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3537
  have eq3570 : False := by grind
  exact eq3570
