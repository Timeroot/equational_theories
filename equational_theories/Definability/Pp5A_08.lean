import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxx_y_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
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
  have eq52 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x y)) := by
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
  have eq53 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq71
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq260 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq271 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq260 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq260
    | exact resolve eq260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq271
    | exact resolve eq271 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq271
  have eq505 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq14
    | exact resolve eq14 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq694 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq16
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq844 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq14
    | exact resolve eq14 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 : G, y = (M.op (M.op x (τ (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq52
    | exact resolve eq52 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq847 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (M.op X0 X0))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq53
    | exact resolve eq53 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq879 : ∀ X0 : G, y = (M.op (M.op x (τ (τ (M.op X0 X0)))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq846 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq846
    | exact resolve eq846 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq896 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (τ (M.op X0 X0)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq847 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq847
    | exact resolve eq847 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq945 : ∀ X0 : G, y = (M.op (M.op x (τ (τ (τ (M.op X0 X0))))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq879 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq879
    | exact resolve eq879 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq955 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (τ (τ (M.op X0 X0))))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq896 (τ X0)
       have i₂ := eq694 X0
       grind)
    | exact superpose eq694 eq896
    | exact resolve eq896 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq896
  have eq2899 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (σ (σ (M.op X0 X0)))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq505 (M.op x (σ (M.op X0 X0))) X1 X3
       have i₂ := eq505 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq505 eq505
    | exact resolve eq505 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6722 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq844 (M.op x (τ (M.op X0 X0))) X1 X3
       have i₂ := eq844 X0 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq844 eq844
    | exact resolve eq844 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15475 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (σ (σ (σ (M.op X0 X0))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2899 (M.op x (σ (M.op X0 X0))) X1 X3
       have i₂ := eq505 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq505 eq2899
    | exact resolve eq2899 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899
  have eq15640 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (M.op X0 X0))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6722 (M.op x (τ (M.op X0 X0))) X1 X3
       have i₂ := eq844 X0 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq844 eq6722
    | exact resolve eq6722 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq6722
  have eq25738 : ∀ X0 : G, y = (M.op (M.op y (σ (M.op X0 X0))) (M.op y x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq505 X0 y y
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq505
    | exact resolve eq505 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq25753 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25738 x
       have i₂ := eq505 x y x
       grind)
    | exact superpose eq505 eq25738
    | exact resolve eq25738 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq25738
  have eq25771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq25753 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq25753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25753
  have eq25772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq25771
    | exact resolve eq25771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25771
  have eq25783 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq25772
       have r₂ := eq27
       grind)
    | exact resolve eq25772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25772
  have eq25787 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq25783
    | exact resolve eq25783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25783
  have eq25914 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ (σ (σ (M.op X0 X0))))) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25787 eq15475
    | exact resolve eq15475 eq25787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25787
  have eq25918 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq25914 x
       have i₂ := eq15475 x sF3 sF2
       grind)
    | (have i₁ := eq25914 x
       have i₂ := eq15475 x x (M.op (M.op sF3 (σ (σ (σ (M.op x x))))) (M.op sF3 sF2))
       grind)
    | exact superpose eq15475 eq25914
    | exact resolve eq25914 eq15475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15475 eq25914
  have eq26057 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (τ (τ (τ (M.op X0 X0))))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25918 eq15640
    | exact resolve eq15640 eq25918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25918
  have eq26061 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq955 eq26057
    | exact resolve eq26057 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq26057
  have eq26062 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq26061
  have eq26440 : ∀ X0 : G, x = (M.op (M.op x (τ (τ (τ (M.op X0 X0))))) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq15640 X0 x x
       have i₂ := eq26062
       grind)
    | exact superpose eq26062 eq15640
    | exact resolve eq15640 eq26062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15640 eq26062
  have eq26444 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq945 eq26440
    | exact resolve eq26440 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq26440
  have eq26445 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq26444
  have eq26517 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq26445 eq29
    | exact resolve eq29 eq26445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26445
  have eq26652 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq26517
    | exact resolve eq26517 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq26517
  have eq26653 : x = y := by grind
  clear eq26652
  have eq26672 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26653
       grind)
    | exact superpose eq26653 eq18
    | exact resolve eq18 eq26653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26673 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq26653
       grind)
    | exact superpose eq26653 eq24
    | exact resolve eq24 eq26653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26653
  have eq26815 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26673
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26673
    | exact resolve eq26673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26673
  have eq27019 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26815 eq26
    | exact resolve eq26 eq26815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq26815
  have eq27456 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27019 eq74
    | exact resolve eq74 eq27019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq27019
  have eq27669 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq27456
       have i₂ := eq26672
       grind)
    | exact superpose eq26672 eq27456
    | exact resolve eq27456 eq26672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26672 eq27456
  have eq27683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27669 eq15
    | exact resolve eq15 eq27669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27669
  have eq27772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq27683
    | exact resolve eq27683 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq27683
  have eq27793 : False := by grind
  exact eq27793

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pyx_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x y)) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq405 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq44
    | (have j1 := eq111 x
       grind)
    | exact resolve eq44 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq3497 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq17888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17888
    | exact resolve eq17888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17888
  have eq17900 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17889
       have r₂ := eq28
       grind)
    | exact resolve eq17889 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17889
  have eq17902 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17900
    | exact resolve eq17900 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17900
  have eq17928 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17902 eq14
    | exact resolve eq14 eq17902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17902
  have eq17932 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq54 eq17928
    | exact resolve eq17928 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17928
  have eq17937 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq17932
  have eq17962 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17937
    | exact resolve eq17937 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17937
  have eq18231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17962 eq89
    | exact resolve eq89 eq17962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq17962
  have eq18239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq18231
  have eq18241 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18239
       have r₂ := eq28
       grind)
    | exact resolve eq18239 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18239
  have eq18267 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 X0)) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq18241
       grind)
    | exact superpose eq18241 eq14
    | exact resolve eq14 eq18241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18241
  have eq18271 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53 eq18267
    | exact resolve eq18267 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq18267
  have eq18277 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18271
  have eq18302 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18277
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18277
    | exact resolve eq18277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18277
  have eq18575 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq18302
       grind)
    | exact superpose eq18302 eq45
    | exact resolve eq45 eq18302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18302
  have eq18593 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18575
    | exact resolve eq18575 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18575
  have eq18627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18593 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18627
    | exact resolve eq18627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627
  have eq18641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18630
       have r₂ := eq28
       grind)
    | exact resolve eq18630 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18630
  have eq18643 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18641
    | exact resolve eq18641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18641
  have eq23028 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq18643 eq14
    | exact resolve eq14 eq18643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18643
  have eq23034 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq54 eq23028
    | exact resolve eq23028 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq23028
  have eq23035 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23034
  have eq23041 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23035
  have eq23071 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq23041
    | exact resolve eq23041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23041
  have eq23357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23071 eq18593
    | exact resolve eq18593 eq23071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18593 eq23071
  have eq23359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23357
  have eq23367 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq23359
       have r₂ := eq28
       grind)
    | exact resolve eq23359 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23359
  have eq23370 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq23367 eq30
    | exact resolve eq30 eq23367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23367
  have eq23493 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq23370
    | exact resolve eq23370 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23370
  have eq23494 : x = y := by grind
  clear eq23493
  have eq23495 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq23494
       grind)
    | exact superpose eq23494 eq19
    | exact resolve eq19 eq23494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq23496 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq23494
       grind)
    | exact superpose eq23494 eq25
    | exact resolve eq25 eq23494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23494
  have eq23634 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq23496
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23496
    | exact resolve eq23496 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23496
  have eq23637 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23634 eq27
    | exact resolve eq27 eq23634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23634
  have eq23767 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq405
       have i₂ := eq23495
       grind)
    | exact superpose eq23495 eq405
    | exact resolve eq405 eq23495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq23773 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  have eq23805 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq23767
    | exact resolve eq23767 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23767
  have eq23813 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq25257 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23805 eq111
    | (have j0 := eq111 (σ x)
       grind)
    | exact resolve eq111 eq23805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq25258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23637 eq25257
    | exact resolve eq25257 eq23637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25257
  have eq25270 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25258
       have r₂ := eq28
       grind)
    | exact resolve eq25258 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25258
  have eq25276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23637 eq25270
    | exact resolve eq25270 eq23637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25270
  have eq25286 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25276 eq23813
    | exact resolve eq23813 eq25276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23813 eq25276
  have eq25290 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23637 eq25286
    | exact resolve eq25286 eq23637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25286
  have eq26389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25290 eq23805
    | exact resolve eq23805 eq25290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23805 eq25290
  have eq26393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26389
  have eq26397 : x = (M.op x y) := by
    first
    | (have r₁ := eq26393
       have r₂ := eq28
       grind)
    | exact resolve eq26393 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26393
  have eq26405 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26397 eq21
    | exact resolve eq21 eq26397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26485 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq26397 eq23773
    | exact resolve eq23773 eq26397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23773
  have eq26492 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq26485
       have i₂ := eq23495
       grind)
    | exact superpose eq23495 eq26485
    | exact resolve eq26485 eq23495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23495 eq26485
  have eq26563 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26405
    | exact resolve eq26405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26405
  have eq26566 : x = (k x x) := by
    first
    | exact superpose eq26397 eq26492
    | exact resolve eq26492 eq26397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26397 eq26492
  have eq26872 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3497 x
       have i₂ := eq26566
       grind)
    | exact superpose eq26566 eq3497
    | (have j0 := eq3497 x
       grind)
    | exact resolve eq3497 eq26566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497 eq26566
  have eq26876 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26872
  have eq26884 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26876
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26876
    | exact resolve eq26876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq26876
  have eq26896 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23637 eq26884
    | exact resolve eq26884 eq23637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23637 eq26884
  have eq26907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26563 eq26896
    | exact resolve eq26896 eq26563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26563 eq26896
  have eq26916 : False := by grind
  exact eq26916

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pxx_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq110
    | (have j0 := eq110 (σ X0)
       grind)
    | exact resolve eq110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq44
    | (have j1 := eq110 x
       grind)
    | exact resolve eq44 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq3505 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq402 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq19342 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 X0)) (M.op y x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq14
    | exact resolve eq14 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq19345 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19342 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq19342
    | exact resolve eq19342 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19342
  have eq19372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq19345 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19372
    | exact resolve eq19372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19372
  have eq19384 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19373
       have r₂ := eq28
       grind)
    | exact resolve eq19373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19373
  have eq19410 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19384 eq14
    | exact resolve eq14 eq19384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19384
  have eq19413 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19410 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq19410
    | exact resolve eq19410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19410
  have eq19517 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq19413
  have eq19543 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19517
    | exact resolve eq19517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19517
  have eq19580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq19543 eq19345
    | exact resolve eq19345 eq19543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19345 eq19543
  have eq19582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq19580
  have eq19584 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19582
       have r₂ := eq28
       grind)
    | exact resolve eq19582 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq19780 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19584
  have eq19805 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19780
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19780
    | exact resolve eq19780 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19780
  have eq20003 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19805
       grind)
    | exact superpose eq19805 eq45
    | exact resolve eq45 eq19805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19805
  have eq20021 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq20003
    | exact resolve eq20003 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20003
  have eq20058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20021 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq20058
    | exact resolve eq20058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20058
  have eq20072 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20061
       have r₂ := eq28
       grind)
    | exact resolve eq20061 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20061
  have eq57175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20072 eq14
    | exact resolve eq14 eq20072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20072
  have eq57189 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57175 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq57175
    | exact resolve eq57175 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57175
  have eq57190 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq57189
  have eq57197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq57190
  have eq57239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq57197
    | exact resolve eq57197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57197
  have eq57262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq57239 eq20021
    | exact resolve eq20021 eq57239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021 eq57239
  have eq57296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq57262
  have eq57308 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57296
       have r₂ := eq28
       grind)
    | exact resolve eq57296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296
  have eq57646 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq57308 eq30
    | exact resolve eq30 eq57308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57308
  have eq57773 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq57646
    | exact resolve eq57646 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq57646
  have eq57774 : x = y := by grind
  clear eq57773
  have eq57775 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq57774
       grind)
    | exact superpose eq57774 eq19
    | exact resolve eq19 eq57774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq57776 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq57774
       grind)
    | exact superpose eq57774 eq25
    | exact resolve eq25 eq57774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq57774
  have eq57991 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq57776
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57776
    | exact resolve eq57776 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57776
  have eq57992 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57991 eq27
    | exact resolve eq27 eq57991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57991
  have eq58563 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq406
       have i₂ := eq57775
       grind)
    | exact superpose eq57775 eq406
    | exact resolve eq406 eq57775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq58574 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  have eq58608 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq58563
    | exact resolve eq58563 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58563
  have eq58616 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq59216 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58608 eq110
    | (have j0 := eq110 (σ x)
       grind)
    | exact resolve eq110 eq58608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq59217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57992 eq59216
    | exact resolve eq59216 eq57992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59216
  have eq59231 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq59217
       have r₂ := eq28
       grind)
    | exact resolve eq59217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59217
  have eq59237 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57992 eq59231
    | exact resolve eq59231 eq57992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59231
  have eq59251 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59237 eq58616
    | exact resolve eq58616 eq59237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58616 eq59237
  have eq59255 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57992 eq59251
    | exact resolve eq59251 eq57992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59251
  have eq59924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59255 eq58608
    | exact resolve eq58608 eq59255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58608 eq59255
  have eq59929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq59924
  have eq59932 : x = (M.op x y) := by
    first
    | (have r₁ := eq59929
       have r₂ := eq28
       grind)
    | exact resolve eq59929 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59929
  have eq59943 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq59932 eq21
    | exact resolve eq21 eq59932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq60068 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq59932 eq58574
    | exact resolve eq58574 eq59932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58574
  have eq60077 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq60068
       have i₂ := eq57775
       grind)
    | exact superpose eq57775 eq60068
    | exact resolve eq60068 eq57775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57775 eq60068
  have eq60188 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59943
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59943
    | exact resolve eq59943 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59943
  have eq60192 : x = (k x x) := by
    first
    | exact superpose eq59932 eq60077
    | exact resolve eq60077 eq59932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59932 eq60077
  have eq60552 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3505 x
       have i₂ := eq60192
       grind)
    | exact superpose eq60192 eq3505
    | (have j0 := eq3505 x
       grind)
    | exact resolve eq3505 eq60192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505 eq60192
  have eq60556 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60552
  have eq60563 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60556
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60556
    | exact resolve eq60556 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq60556
  have eq60578 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57992 eq60563
    | exact resolve eq60563 eq57992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57992 eq60563
  have eq60591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60188 eq60578
    | exact resolve eq60578 eq60188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60188 eq60578
  have eq60602 : False := by grind
  exact eq60602

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq232 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq235 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq586 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y X0
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y) X0
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq638 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq586 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq586
    | exact resolve eq586 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq1249 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq235
    | exact resolve eq235 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1259 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1249 eq14
    | exact resolve eq14 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1441 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq598 X0
       have i₂ := eq232 x
       grind)
    | exact superpose eq232 eq598
    | exact resolve eq598 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1446 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1441 eq14
    | exact resolve eq14 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1515 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq599 X0
       have i₂ := eq232 sF2
       grind)
    | exact superpose eq232 eq599
    | exact resolve eq599 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq599
  have eq1523 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1515 eq1259
    | exact resolve eq1259 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq1515
  have eq9898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq9899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9898
    | exact resolve eq9898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9898
  have eq9910 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9899
       have r₂ := eq28
       grind)
    | exact resolve eq9899 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9899
  have eq9914 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9910
    | exact resolve eq9910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9910
  have eq9977 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9914 eq638
    | exact resolve eq638 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq9984 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1523 eq9977
    | exact resolve eq9977 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523 eq9977
  have eq9985 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9984
  have eq10059 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq638 y y x
       have i₂ := eq9985
       grind)
    | exact superpose eq9985 eq638
    | exact resolve eq638 eq9985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq9985
  have eq10066 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1446 eq10059
    | exact resolve eq10059 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq10059
  have eq10067 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10066
  have eq10093 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10067 eq30
    | exact resolve eq30 eq10067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10067
  have eq10200 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq10093
    | exact resolve eq10093 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10093
  have eq10201 : x = y := by grind
  clear eq10200
  have eq10216 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10201
       grind)
    | exact superpose eq10201 eq19
    | exact resolve eq19 eq10201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10217 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10201
       grind)
    | exact superpose eq10201 eq25
    | exact resolve eq25 eq10201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq10201
  have eq10328 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10217
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10217
    | exact resolve eq10217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10217
  have eq10345 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10328 eq27
    | exact resolve eq27 eq10328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10328
  have eq10967 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10345 eq72
    | exact resolve eq72 eq10345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq10345
  have eq11069 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10967
       have i₂ := eq10216
       grind)
    | exact superpose eq10216 eq10967
    | exact resolve eq10967 eq10216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10216 eq10967
  have eq11078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11069 eq15
    | exact resolve eq15 eq11069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq11121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11078
    | exact resolve eq11078 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11078
  have eq11130 : False := by grind
  exact eq11130

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq186 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq540 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq548 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq540 X0 X1 X2
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq540
    | exact resolve eq540 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq591 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq183
    | exact resolve eq183 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq186
  have eq645 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq548 eq16
    | exact resolve eq16 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq591 eq645
    | exact resolve eq645 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq882 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq949 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq949 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq949 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq949 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1058 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq882
       grind)
    | exact superpose eq882 eq41
    | exact resolve eq41 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq1059 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1058
    | exact resolve eq1058 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1061 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq1059
    | exact resolve eq1059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1061 eq883
    | exact resolve eq883 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1069
       have r₂ := eq27
       grind)
    | exact resolve eq1069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1082 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1076 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1076
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1076
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1076
       grind)
    | exact resolve eq12 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1076 eq548
    | exact resolve eq548 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1076 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1085
    | exact resolve eq1085 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1089 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq591 eq1084
    | exact resolve eq1084 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1090 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1082
       have r₂ := eq26
       grind)
    | exact resolve eq1082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1082
  have eq1093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1061 eq1088
    | exact resolve eq1088 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1094 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1089 x
       have i₂ := eq655 (M.op sF3 sF2) sF4 x
       grind)
    | exact superpose eq655 eq1089
    | exact resolve eq1089 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1095 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq954 sF3
       grind)
    | exact superpose eq954 eq1090
    | exact resolve eq1090 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1097 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1093
       have r₂ := eq27
       grind)
    | exact resolve eq1093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1098 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1076 eq1094
    | exact resolve eq1094 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1094
  have eq1099 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1061 eq1095
    | exact resolve eq1095 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq1095
  have eq1101 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1099
       have r₂ := eq1097
       grind)
    | exact resolve eq1099 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq1099
  have eq1120 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1098 eq548
    | exact resolve eq548 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq591 eq1120
    | exact resolve eq1120 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1133 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1098 eq1131
    | exact resolve eq1131 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq1131
  have eq1134 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1133
       have i₂ := eq954 sF3
       grind)
    | exact superpose eq954 eq1133
    | exact resolve eq1133 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1101 eq1134
    | exact resolve eq1134 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq1134
  have eq1136 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1135
       have r₂ := eq27
       grind)
    | exact resolve eq1135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1141 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1136
       grind)
    | exact superpose eq1136 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1136
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1136
       grind)
    | exact resolve eq12 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1143 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq548 y x x
       have i₂ := eq1136
       grind)
    | exact superpose eq1136 eq548
    | exact resolve eq548 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1136
       grind)
    | exact superpose eq1136 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1147 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1144
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1144
    | exact resolve eq1144 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1148 : y = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1143 x
       have i₂ := eq655 sF0 sF0 x
       grind)
    | exact superpose eq655 eq1143
    | exact resolve eq1143 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1149 : x = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have r₁ := eq1141
       have r₂ := eq18
       grind)
    | exact resolve eq1141 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1141
  have eq1154 : (k x y) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1149
       have i₂ := eq954 y
       grind)
    | exact superpose eq954 eq1149
    | exact resolve eq1149 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1159 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | exact superpose eq1148 eq548
    | exact resolve eq548 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq591 eq1159
    | exact resolve eq1159 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1172 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1148 eq1170
    | exact resolve eq1170 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq1170
  have eq1173 : (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq1172
       have i₂ := eq954 y
       grind)
    | exact superpose eq954 eq1172
    | exact resolve eq1172 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1175 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq41
    | exact resolve eq41 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1175
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1175
    | exact resolve eq1175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1175
  have eq1179 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq1177
    | exact resolve eq1177 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1283 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1173
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq1173
    | exact resolve eq1173 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq1173
  have eq1291 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq1283
       have r₂ := eq1147
       grind)
    | exact resolve eq1283 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq1283
  have eq1300 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1291
       grind)
    | exact superpose eq1291 eq41
    | exact resolve eq41 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1291
  have eq1301 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1300
    | exact resolve eq1300 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1300
  have eq1303 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1301
    | exact resolve eq1301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1301
  have eq1306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1303 eq883
    | exact resolve eq883 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq1303
  have eq1313 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1306
       have r₂ := eq27
       grind)
    | exact resolve eq1306 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1321 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1313 eq548
    | exact resolve eq548 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq591 eq1321
    | exact resolve eq1321 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1331 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1326 x
       have i₂ := eq655 (M.op sF3 sF2) sF4 x
       grind)
    | exact superpose eq655 eq1326
    | exact resolve eq1326 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq1326
  have eq1335 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1313 eq1331
    | exact resolve eq1331 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq1331
  have eq1340 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1335 eq548
    | exact resolve eq548 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1351 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq591 eq1340
    | exact resolve eq1340 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq1340
  have eq1353 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1335 eq1351
    | exact resolve eq1351 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335 eq1351
  have eq1354 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1353
       have i₂ := eq954 sF3
       grind)
    | exact superpose eq954 eq1353
    | exact resolve eq1353 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq1353
  have eq1355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1179 eq1354
    | exact resolve eq1354 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq1354
  have eq1356 : False := by grind
  exact eq1356

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  clear eq22
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
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
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq181 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq186 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq551 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq559 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq551 X0 X1 X2
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq551
    | exact resolve eq551 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq602 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq183
    | exact resolve eq183 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq186
  have eq656 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq559 eq16
    | exact resolve eq16 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq602 eq656
    | exact resolve eq656 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq723 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq724 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq793 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq793 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq793 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq793 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq911 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq40
    | exact resolve eq40 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq912 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq911
    | exact resolve eq911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq914 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq912
    | exact resolve eq912 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq914 eq724
    | exact resolve eq724 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq922
       have r₂ := eq27
       grind)
    | exact resolve eq922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq934 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq929 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq929
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq929
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq929
       grind)
    | exact resolve eq12 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq929 eq559
    | exact resolve eq559 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq602 eq937
    | exact resolve eq937 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq943 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq934
       have r₂ := eq26
       grind)
    | exact resolve eq934 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq945 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq941 x
       have i₂ := eq666 (M.op sF3 sF2) sF4 x
       grind)
    | exact superpose eq666 eq941
    | exact resolve eq941 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq947 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq943
    | exact resolve eq943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq943
  have eq948 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq929 eq945
    | exact resolve eq945 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq945
  have eq949 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq947
       have i₂ := eq798 sF3
       grind)
    | exact superpose eq798 eq947
    | exact resolve eq947 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq950 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq914 eq949
    | exact resolve eq949 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq953 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq948 eq559
    | exact resolve eq559 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq602 eq953
    | exact resolve eq953 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq966 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq948 eq964
    | exact resolve eq964 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq964
  have eq967 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq966
       have i₂ := eq798 sF3
       grind)
    | exact superpose eq798 eq966
    | exact resolve eq966 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq950 eq967
    | exact resolve eq967 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq967
  have eq987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq982
  have eq992 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq987
       have r₂ := eq27
       grind)
    | exact resolve eq987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq999 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq992
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq992
       grind)
    | exact resolve eq12 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq559 y x x
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq559
    | exact resolve eq559 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1006 : y = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1002 x
       have i₂ := eq666 sF0 sF0 x
       grind)
    | exact superpose eq666 eq1002
    | exact resolve eq1002 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1008 : y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq999
       have r₂ := eq18
       grind)
    | exact resolve eq999 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1013 : y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1008
    | exact resolve eq1008 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1014 : (k y x) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq798 y
       grind)
    | exact superpose eq798 eq1013
    | exact resolve eq1013 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1017 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1006 eq559
    | exact resolve eq559 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq602 eq1017
    | exact resolve eq1017 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1030 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1006 eq1028
    | exact resolve eq1028 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq1028
  have eq1031 : (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq798 y
       grind)
    | exact superpose eq798 eq1030
    | exact resolve eq1030 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1035 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1031
       grind)
    | exact superpose eq1031 eq41
    | exact resolve eq41 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1037 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1035
    | exact resolve eq1035 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1039 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1037
    | exact resolve eq1037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1218 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq1031
    | exact resolve eq1031 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq1031
  have eq1225 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1218
  have eq1231 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1225
       have r₂ := eq180
       grind)
    | exact resolve eq1225 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1225
  have eq1240 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1231
       grind)
    | exact superpose eq1231 eq40
    | exact resolve eq40 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1231
  have eq1241 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1240
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1240
    | exact resolve eq1240 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1243 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1241
    | exact resolve eq1241 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1243 eq724
    | exact resolve eq724 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq1243
  have eq1253 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1246
       have r₂ := eq27
       grind)
    | exact resolve eq1246 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1588 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1253 eq559
    | exact resolve eq559 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1590 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq602 eq1588
    | exact resolve eq1588 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1597 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1590 x
       have i₂ := eq666 (M.op sF3 sF2) sF4 x
       grind)
    | exact superpose eq666 eq1590
    | exact resolve eq1590 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1602 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1253 eq1597
    | exact resolve eq1597 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq1597
  have eq1653 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1602 eq559
    | exact resolve eq559 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1670 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq602 eq1653
    | exact resolve eq1653 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq1672 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1602 eq1670
    | exact resolve eq1670 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq1670
  have eq1673 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1672
       have i₂ := eq798 sF3
       grind)
    | exact superpose eq798 eq1672
    | exact resolve eq1672 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1039 eq1673
    | exact resolve eq1673 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq1673
  have eq1675 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1674
       have r₂ := eq27
       grind)
    | exact resolve eq1674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1676 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1675 eq27
    | exact resolve eq27 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1678 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1675 eq181
    | (have r₁ := eq181
       have r₂ := eq1675
       grind)
    | exact resolve eq181 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1687 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq1678
  have eq1699 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1687 eq914
    | exact resolve eq914 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1703 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | exact superpose eq1687 eq142
    | exact resolve eq142 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1687
  have eq1704 : y = (k y x) := by
    first
    | exact superpose eq32 eq1703
    | exact resolve eq1703 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1703
  have eq1707 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1699
       have r₂ := eq1676
       grind)
    | exact resolve eq1699 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq1723 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1707
       grind)
    | exact superpose eq1707 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1707
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1707
       grind)
    | exact resolve eq12 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1729 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq559 y x x
       have i₂ := eq1707
       grind)
    | exact superpose eq1707 eq559
    | exact resolve eq559 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1731 : y = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1729 x
       have i₂ := eq666 sF0 sF0 x
       grind)
    | exact superpose eq666 eq1729
    | exact resolve eq1729 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq1729
  have eq1735 : y = (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq1723
       have r₂ := eq18
       grind)
    | exact resolve eq1723 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq1740 : y = (M.op (M.op (M.op x y) (σ x)) (σ y)) := by
    first
    | exact superpose eq1675 eq1731
    | exact resolve eq1731 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1743 : y = (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq1735
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1735
    | exact resolve eq1735 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1735
  have eq1746 : (k y x) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1743
       have i₂ := eq798 y
       grind)
    | exact superpose eq798 eq1743
    | exact resolve eq1743 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1747 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1746
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq1746
    | exact resolve eq1746 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704 eq1746
  have eq1750 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | exact superpose eq1740 eq559
    | exact resolve eq559 eq1740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq1766 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq602 eq1750
    | exact resolve eq1750 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq1750
  have eq1771 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (σ x)) (σ y)) y) := by
    first
    | exact superpose eq1675 eq1766
    | exact resolve eq1766 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675 eq1766
  have eq1772 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1740 eq1771
    | exact resolve eq1771 eq1740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740 eq1771
  have eq1773 : (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq1772
       have i₂ := eq798 y
       grind)
    | exact superpose eq798 eq1772
    | exact resolve eq1772 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq1772
  have eq1836 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1773
       have i₂ := eq1747
       grind)
    | exact superpose eq1747 eq1773
    | exact resolve eq1773 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq1773
  have eq1848 : y = (M.op x y) := by grind
  clear eq1836
  have eq1857 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1848
       grind)
    | exact superpose eq1848 eq24
    | exact resolve eq24 eq1848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1848
  have eq1878 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1857 eq20
    | exact resolve eq20 eq1857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1857
  have eq1898 : False := by grind
  exact eq1898

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq33 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X1 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq52 X0 (M.op X1 X1)
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq47 (k X1 X1) X1
       grind)
    | exact resolve eq52 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq52
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq64
    | exact resolve eq64 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq223 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq468 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (M.op (σ X0) (σ X1)) X2) (M.op X2 X3)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq58 (σ X0) (σ X1) X2 X3
       grind)
    | exact superpose eq58 eq15
    | (have j1 := eq58 (σ X0) (σ X1) X2 X3
       grind)
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2251 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X1 X0 x (M.op X1 X0)
       have i₂ := eq58 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq58 eq223
    | (have j1 := eq58 X1 X0 x x
       grind)
    | exact resolve eq223 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq2301 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2251 X0 X1
       have j1 := eq147 X0 X1
       grind)
    | (have r₁ := eq2251 X0 X1
       have r₂ := eq147 X0 X1
       grind)
    | (have r₁ := eq2251 X1 X0
       have r₂ := eq147 X0 X1
       grind)
    | exact resolve eq2251 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq2251
  have eq3299 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq3300 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3299 X0 X1
       have i₂ := eq2301 X0 X1
       grind)
    | exact superpose eq2301 eq3299
    | (have j0 := eq3299 X0 X1
       grind)
    | exact resolve eq3299 eq2301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3299
  have eq6707 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (σ X1) (σ X0) x (M.op (σ X1) (σ X0))
       have i₂ := eq468 X1 X0 (M.op (σ X1) (σ X0)) (M.op (σ X0) x)
       grind)
    | exact superpose eq468 eq223
    | (have j1 := eq468 X1 X0 x x
       grind)
    | exact resolve eq223 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq468
  have eq6849 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6707 X0 X1
       have i₂ := eq2301 X0 X1
       grind)
    | exact superpose eq2301 eq6707
    | (have j0 := eq6707 X0 X1
       grind)
    | exact resolve eq6707 eq2301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301 eq6707
  have eq6976 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6849 X0 X1
       have j1 := eq3300 X0 X1
       grind)
    | (have r₁ := eq6849 X0 X1
       have r₂ := eq3300 X0 X1
       grind)
    | (have r₁ := eq6849 X1 X0
       have r₂ := eq3300 X0 X1
       grind)
    | exact resolve eq6849 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq6849
  have eq7040 : False := by grind
  exact eq7040

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq182 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq715 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq182
    | exact resolve eq182 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq716 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq715
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq715
    | exact resolve eq715 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq716
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq716
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq716 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq716
  have eq754 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq753
  have eq10157 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq10
    | exact resolve eq10 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq10196 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10157
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq10157
    | exact resolve eq10157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10157
  have eq10197 : (M.op y y) = (M.op x x) := by grind
  clear eq10196
  have eq10408 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq106 y y x
       have i₂ := eq10197
       grind)
    | exact superpose eq10197 eq106
    | exact resolve eq106 eq10197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq10197
  have eq10451 : x = y := by
    first
    | (have i₁ := eq10408 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq10408
    | exact resolve eq10408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10408
  have eq10557 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10451
       grind)
    | exact superpose eq10451 eq16
    | exact resolve eq16 eq10451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10451
  have eq10558 : False := by grind
  exact eq10558
