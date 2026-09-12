import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_x_pyx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
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
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  clear eq71
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq103 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq107 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq103
    | exact resolve eq103 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq107
    | exact resolve eq107 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq107
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq241 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq645 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq51
    | exact resolve eq51 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1805 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq557 X0 X0 X0
       grind)
    | exact superpose eq557 eq14
    | exact resolve eq14 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq557 X0 X0 X0
       grind)
    | exact superpose eq557 eq51
    | exact resolve eq51 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1819 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq589 (M.op x (M.op x x)) x
       have i₂ := eq557 x x x
       grind)
    | exact superpose eq557 eq589
    | exact resolve eq589 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq589
  have eq2088 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq505 X0
       have i₂ := eq1806 X0
       grind)
    | exact superpose eq1806 eq505
    | exact resolve eq505 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2113 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq52 sF4
       have i₂ := eq1806 sF4
       grind)
    | exact superpose eq1806 eq52
    | exact resolve eq52 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1806
  have eq2161 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq645 eq2088
    | exact resolve eq2088 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq2088
  have eq2764 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq1819 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1819
    | (have j0 := eq1819 y x
       grind)
    | exact resolve eq1819 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq6504 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op X0 X1) (M.op y y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq579
    | exact resolve eq579 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6572 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op X0 X1) (M.op y y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq241 eq6504
    | exact resolve eq6504 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504
  have eq28418 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq505 X2
       have i₂ := eq1805 X2 X0 X1
       grind)
    | exact superpose eq1805 eq505
    | exact resolve eq505 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28510 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq579 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1805 X0 X0 X1
       grind)
    | exact superpose eq1805 eq579
    | exact resolve eq579 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq28597 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28510 X0 X1 x x x
       have i₂ := eq579 X0 X0 x x x
       grind)
    | exact superpose eq579 eq28510
    | exact resolve eq28510 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq28510
  have eq31029 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6572 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq505 X0
       grind)
    | exact superpose eq505 eq6572
    | exact resolve eq6572 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6572
  have eq39122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39122
    | exact resolve eq39122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39122
  have eq39134 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq39123
       have r₂ := eq28
       grind)
    | exact resolve eq39123 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39123
  have eq39138 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39134
    | exact resolve eq39134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39134
  have eq39142 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39138 eq65
    | (have r₁ := eq65
       have r₂ := eq39138
       grind)
    | exact resolve eq65 eq39138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq39153 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39138 eq51
    | exact resolve eq51 eq39138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39138
  have eq39261 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq39142
  have eq39586 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39153 eq2113
    | exact resolve eq2113 eq39153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113 eq39153
  have eq39937 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39261 eq90
    | exact resolve eq90 eq39261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq39261
  have eq39949 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq39937
  have eq40233 : (τ (σ x)) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq39949 eq127
    | exact resolve eq127 eq39949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39949
  have eq40383 : x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq29 eq40233
    | exact resolve eq40233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40233
  have eq40384 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq40383
  have eq40409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40384 eq39586
    | exact resolve eq39586 eq40384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39586 eq40384
  have eq40451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq40409
  have eq40459 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq40451
       have r₂ := eq28
       grind)
    | exact resolve eq40451 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40451
  have eq40464 : (τ (σ x)) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40459 eq127
    | exact resolve eq127 eq40459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq40459
  have eq40614 : x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq40464
    | exact resolve eq40464 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40464
  have eq40615 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq40614
  have eq40928 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq40615
       grind)
    | exact superpose eq40615 eq73
    | exact resolve eq73 eq40615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq40940 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq40615
       grind)
    | exact superpose eq40615 eq51
    | exact resolve eq51 eq40615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq41042 : ∀ X0 : G, (M.op X0 (M.op x (M.op (M.op x y) X0))) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq28418 x x X0
       have i₂ := eq40615
       grind)
    | exact superpose eq40615 eq28418
    | exact resolve eq28418 eq40615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28418 eq40615
  have eq41093 : x = (M.op y (M.op y (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq241 eq40940
    | exact resolve eq40940 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq40940
  have eq41102 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq40928
    | exact resolve eq40928 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40928
  have eq49636 : (M.op y (M.op y y)) = (M.op (M.op y (M.op y y)) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2764 eq41042
    | exact resolve eq41042 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764 eq41042
  have eq49800 : (M.op y (M.op y y)) = (M.op (M.op y (M.op y y)) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq49636
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49636
    | exact resolve eq49636 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49636
  have eq49827 : (M.op y (M.op x y)) = (M.op y (M.op y y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31029 eq49800
    | exact resolve eq49800 eq31029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31029 eq49800
  have eq62526 : y = (M.op y (M.op y (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq505 y
       have i₂ := eq49827
       grind)
    | exact superpose eq49827 eq505
    | exact resolve eq505 eq49827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq49827
  have eq63748 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq62526 eq41093
    | exact resolve eq41093 eq62526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41093 eq62526
  have eq63808 : x = (M.op y y) ∨ x = y := by grind
  clear eq63748
  have eq64130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2161 y
       have i₂ := eq63808
       grind)
    | exact superpose eq63808 eq2161
    | exact resolve eq2161 eq63808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq64199 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28597 y y
       have i₂ := eq63808
       grind)
    | exact superpose eq63808 eq28597
    | exact resolve eq28597 eq63808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28597 eq63808
  have eq64202 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq64199
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64199
    | exact resolve eq64199 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64199
  have eq64230 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq64130
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64130
    | exact resolve eq64130 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64130
  have eq64273 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq64230
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64230
    | exact resolve eq64230 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64230
  have eq64294 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq64273
    | exact resolve eq64273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64273
  have eq64303 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq64202 eq21
    | exact resolve eq21 eq64202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64202
  have eq64605 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq64303
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64303
    | exact resolve eq64303 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64303
  have eq64642 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq64294 eq28
    | exact resolve eq28 eq64294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64294
  have eq64961 : x = y := by
    first
    | (have r₁ := eq64642
       have r₂ := eq64605
       grind)
    | exact resolve eq64642 eq64605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64605 eq64642
  have eq64963 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq64961
       grind)
    | exact superpose eq64961 eq19
    | exact resolve eq19 eq64961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq64964 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq64961
       grind)
    | exact superpose eq64961 eq25
    | exact resolve eq25 eq64961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq65251 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq64964
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64964
    | exact resolve eq64964 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64964
  have eq65312 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq65251 eq27
    | exact resolve eq27 eq65251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq65251
  have eq65999 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq65312 eq72
    | exact resolve eq72 eq65312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq66010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq65312 eq41102
    | exact resolve eq41102 eq65312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41102 eq65312
  have eq66242 : x = (M.op y y) := by
    first
    | (have r₁ := eq66010
       have r₂ := eq28
       grind)
    | exact resolve eq66010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66010
  have eq66253 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq65999
       have i₂ := eq64963
       grind)
    | exact superpose eq64963 eq65999
    | exact resolve eq65999 eq64963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65999
  have eq66300 : x = (M.op x x) := by
    first
    | (have i₁ := eq66242
       have i₂ := eq64961
       grind)
    | exact superpose eq64961 eq66242
    | exact resolve eq66242 eq64961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64961 eq66242
  have eq66334 : x = (M.op x y) := by
    first
    | (have i₁ := eq66300
       have i₂ := eq64963
       grind)
    | exact superpose eq64963 eq66300
    | exact resolve eq66300 eq64963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64963 eq66300
  have eq66363 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq66334 eq21
    | exact resolve eq21 eq66334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq66806 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq66363
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq66363
    | exact resolve eq66363 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66363
  have eq67691 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq66334 eq66253
    | exact resolve eq66253 eq66334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66253 eq66334
  have eq67698 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67691 eq15
    | exact resolve eq15 eq67691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67691
  have eq67827 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67698
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq67698
    | exact resolve eq67698 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq67698
  have eq67881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66806 eq67827
    | exact resolve eq67827 eq66806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66806 eq67827
  have eq67932 : False := by grind
  exact eq67932

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq21 X0 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq15
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq74
    | exact resolve eq74 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq74
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq21 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq21
    | exact resolve eq21 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq9
    | exact resolve eq9 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq93 (M.op X0 X0)
       grind)
    | exact superpose eq93 eq9
    | exact resolve eq9 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq150 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq147 X0
       have i₂ := eq21 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq21 eq147
    | exact resolve eq147 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq151 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq21 X0 X0
       grind)
    | exact superpose eq21 eq150
    | exact resolve eq150 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq150
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq212 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq85 X1
       grind)
    | exact superpose eq85 eq201
    | (have j0 := eq201 X0 X1
       grind)
    | exact resolve eq201 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq85 X1
       grind)
    | exact superpose eq85 eq212
    | (have j0 := eq212 X0 X1
       grind)
    | exact resolve eq212 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq222 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq218
    | (have j0 := eq218 X0 X1
       grind)
    | exact resolve eq218 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq231 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq94 X0 X0
       grind)
    | exact superpose eq94 eq94
    | exact resolve eq94 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq94 X0 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq604 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq249 X2 X0 X1
       grind)
    | exact superpose eq249 eq66
    | exact resolve eq66 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq249
  have eq697 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq604 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq604
    | exact resolve eq604 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq604 x x (σ (M.op X0 X0))
       have i₂ := eq103 X0 x x
       grind)
    | exact superpose eq103 eq604
    | exact resolve eq604 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq604
  have eq1911 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq222 x y
       grind)
    | exact superpose eq222 eq16
    | (have j1 := eq222 x y
       grind)
    | exact resolve eq16 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq5212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1911
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1911
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1911 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq5213 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq5212
  have eq5392 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1
       have i₂ := eq231 X1 X0
       grind)
    | exact superpose eq231 eq151
    | exact resolve eq151 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq231
  have eq130216 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5213
       grind)
    | exact superpose eq5213 eq10
    | exact resolve eq10 eq5213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5213
  have eq130342 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq130216
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq130216
    | exact resolve eq130216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130216
  have eq130343 : (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq130342
  have eq1127004 : (M.op y y) = (τ (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq130343
       grind)
    | exact superpose eq130343 eq10
    | exact resolve eq10 eq130343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130343
  have eq1127768 : x = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1127004
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1127004
    | exact resolve eq1127004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127004
  have eq1127769 : (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq1127768
  have eq1128717 : y = (M.op (M.op x x) (M.op (M.op y (M.op x x)) (M.op x x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5392 y y
       have i₂ := eq1127769
       grind)
    | exact superpose eq1127769 eq5392
    | exact resolve eq5392 eq1127769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392 eq1127769
  have eq1128997 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1128717
       have i₂ := eq9 x (M.op x x) y
       grind)
    | exact superpose eq9 eq1128717
    | exact resolve eq1128717 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128717
  have eq1129330 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq697 y
       have i₂ := eq1128997
       grind)
    | exact superpose eq1128997 eq697
    | exact resolve eq697 eq1128997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1129331 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq699 y
       have i₂ := eq1128997
       grind)
    | exact superpose eq1128997 eq699
    | exact resolve eq699 eq1128997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq1128997
  have eq1150019 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1129331
       grind)
    | exact superpose eq1129331 eq16
    | exact resolve eq16 eq1129331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129331
  have eq1150711 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1150019
       have i₂ := eq1129330
       grind)
    | exact superpose eq1129330 eq1150019
    | exact resolve eq1150019 eq1129330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129330 eq1150019
  have eq1150712 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq1150711
  have eq1150713 : x = y := by grind
  clear eq1150712
  have eq1150716 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1150713
       grind)
    | exact superpose eq1150713 eq16
    | exact resolve eq16 eq1150713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150713
  have eq1150717 : False := by grind
  exact eq1150717

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21
    | exact resolve eq21 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq47 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq18
    | exact resolve eq18 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq48 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq67 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq85 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq31
    | exact resolve eq31 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq95 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq95
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq96
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq166 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq104 X0 X0
       grind)
    | exact superpose eq104 eq104
    | exact resolve eq104 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq104 X0 X0
       grind)
    | exact superpose eq104 eq9
    | exact resolve eq9 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq104 X1 X1
       grind)
    | exact superpose eq104 eq114
    | exact resolve eq114 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq104 X1 X0
       grind)
    | exact superpose eq104 eq9
    | exact resolve eq9 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq175 X2 X3 X4
       have i₂ := eq175 X2 X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X2 X2))
       have i₂ := eq104 X2 X0
       grind)
    | exact superpose eq104 eq175
    | exact resolve eq175 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq241 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X2 X3
       have i₂ := eq175 X2 X0 X1
       grind)
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X2
       have i₂ := eq175 X2 X0 X1
       grind)
    | exact superpose eq175 eq98
    | exact resolve eq98 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq245 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 X2 X2
       have i₂ := eq175 X2 X0 X1
       grind)
    | exact superpose eq175 eq114
    | exact resolve eq114 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq251 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq175 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq175 eq9
    | exact resolve eq9 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq182 X2 X3 X2
       have i₂ := eq175 X2 X0 X1
       grind)
    | exact superpose eq175 eq182
    | exact resolve eq182 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq446 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq446
    | (have j0 := eq446 (σ X0)
       grind)
    | exact resolve eq446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq446 (σ X0)
       grind)
    | exact superpose eq446 eq31
    | (have j1 := eq446 (σ X0)
       grind)
    | exact resolve eq31 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq446 (τ X0)
       grind)
    | exact superpose eq446 eq18
    | (have j1 := eq446 (τ X0)
       grind)
    | exact resolve eq18 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq477 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq476 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq476
    | (have j0 := eq476 X0
       grind)
    | exact resolve eq476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq478 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq474 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq474
    | (have j0 := eq474 X0
       grind)
    | exact resolve eq474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq855 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99 X2 X2 X3 X4
       have i₂ := eq175 X2 X0 X1
       grind)
    | exact superpose eq175 eq99
    | exact resolve eq99 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X0 (M.op X1 X0) X2 X3
       have i₂ := eq175 X0 X0 X1
       grind)
    | exact superpose eq175 eq99
    | exact resolve eq99 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq957 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq908 X0 X1 x x
       have i₂ := eq99 X0 X0 x x
       grind)
    | exact superpose eq99 eq908
    | exact resolve eq908 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1316 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq241 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq166 X0 X3
       grind)
    | exact superpose eq166 eq241
    | exact resolve eq241 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1522 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X4 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 X4)) X4 X3
       have i₂ := eq227 (M.op X3 X4) X2 (M.op X2 (M.op X3 X4)) X0 X1
       grind)
    | (have i₁ := eq9 (M.op X2 (M.op X3 X4)) X4 X3
       have i₂ := eq227 X0 X1 (M.op X2 (M.op X3 X4)) (M.op X3 X4) X2
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1620 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq855 X1 X0
       grind)
    | (have i₁ := eq9 X0 (σ X0) (σ X1)
       have i₂ := eq855 X0 X1
       grind)
    | exact superpose eq855 eq9
    | (have j1 := eq855 X1 X0
       grind)
    | exact resolve eq9 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1621 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq855 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq855 X0 X1
       grind)
    | exact superpose eq855 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq855 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq855 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq855 X0 X1
       grind)
    | exact resolve eq13 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq1639 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1640 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1639 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1646 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1640 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1640
    | (have j0 := eq1640 X0 X1
       grind)
    | exact resolve eq1640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq1694 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq233 (M.op X4 X0) (M.op X1 (M.op (M.op X2 X1) X0)) X3
       have i₂ := eq241 X1 X2 X0 X4
       grind)
    | exact superpose eq241 eq233
    | exact resolve eq233 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1813 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1694 X0 X1 X2 X3 X4
       have i₂ := eq95 X4 X0
       grind)
    | exact superpose eq95 eq1694
    | exact resolve eq1694 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1844 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1813 X0 X1 X2 X3 X4
       have i₂ := eq95 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq95 eq1813
    | exact resolve eq1813 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq1855 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1844 X0 X1 X2 X3 X4
       have i₂ := eq241 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq241 eq1844
    | exact resolve eq1844 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1859 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1855 X0 x x X3 X4
       have i₂ := eq245 x x X0
       grind)
    | exact superpose eq245 eq1855
    | exact resolve eq1855 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq1855
  have eq1993 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1859 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq233 X1 X0 x
       grind)
    | exact superpose eq233 eq1859
    | exact resolve eq1859 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq2063 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1993 X0 X1 X2
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq1993
    | exact resolve eq1993 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq2080 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2063 X0 X1 X2
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq2063
    | exact resolve eq2063 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq2063
  have eq3055 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq182 X1 x X0
       grind)
    | exact superpose eq182 eq251
    | exact resolve eq251 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3077 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq251 X0 X2 (M.op X1 (M.op X2 X0)) X0
       have i₂ := eq243 (M.op X2 X0) X1 X0
       grind)
    | exact superpose eq243 eq251
    | exact resolve eq251 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq251
  have eq3157 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3055 X0 X1
       have i₂ := eq2080 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2080 eq3055
    | exact resolve eq3055 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3470 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3157 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq233 X1 X0 (M.op X1 X1)
       grind)
    | exact superpose eq233 eq3157
    | exact resolve eq3157 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq3544 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq241 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq3157 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq3157 eq241
    | exact resolve eq241 eq3157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3568 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3544 X0 X1 X2
       have i₂ := eq2080 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2080 eq3544
    | exact resolve eq3544 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq3603 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3470 X0 X1
       have i₂ := eq2080 X0 X1 X1
       grind)
    | exact superpose eq2080 eq3470
    | exact resolve eq3470 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq3634 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3603 X0 X1
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq3603
    | exact resolve eq3603 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq3603
  have eq3696 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3634 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq241 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq241 eq3634
    | exact resolve eq3634 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634
  have eq3987 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3157 X2 X1
       have i₂ := eq3696 X2 X1 X0
       grind)
    | (have i₁ := eq3157 X0 X1
       have i₂ := eq3696 X0 X1 X1
       grind)
    | exact superpose eq3696 eq3157
    | exact resolve eq3157 eq3696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157 eq3696
  have eq5010 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3568 X1 X3 (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0)
       have i₂ := eq241 (M.op X3 (M.op X1 X1)) X2 X0 (M.op X2 (M.op X3 (M.op X1 X1)))
       grind)
    | exact superpose eq241 eq3568
    | exact resolve eq3568 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq5057 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq3568 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq3568 eq99
    | exact resolve eq99 eq3568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq3568
  have eq5080 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5057 X0 X1 X2 X3
       have i₂ := eq2080 X3 X2 X2
       grind)
    | exact superpose eq2080 eq5057
    | exact resolve eq5057 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5057
  have eq6609 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq469 X0
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq469
    | (have j0 := eq469 X0
       have j1 := eq446 (σ X0)
       grind)
    | exact resolve eq469 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq469
  have eq7438 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq477 X0
       grind)
    | exact superpose eq477 eq10
    | (have j1 := eq477 X0
       grind)
    | exact resolve eq10 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq7724 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5010 X2 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3 X4
       have i₂ := eq333 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq333 eq5010
    | exact resolve eq5010 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq5010
  have eq7773 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7724 X0 X1 X2 X3 X4
       have i₂ := eq2080 X1 X0 X0
       grind)
    | exact superpose eq2080 eq7724
    | exact resolve eq7724 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7724
  have eq7843 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7773 X0 X1 X2 X3 X4
       have i₂ := eq5080 X2 X1 X0 X1
       grind)
    | exact superpose eq5080 eq7773
    | exact resolve eq7773 eq5080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080 eq7773
  have eq13670 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq13778 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1646 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq25363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq907 X3 X2 (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) X4 X5
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq907
    | exact resolve eq907 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25432 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq907 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq227 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq907 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq227 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq227 eq907
    | exact resolve eq907 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq907
  have eq25884 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq25432 X0 X1 x x x X5 X6
       have i₂ := eq7843 x X5 X6 x x
       grind)
    | exact superpose eq7843 eq25432
    | exact resolve eq25432 eq7843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7843 eq25432
  have eq25937 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25363 X0 X1 X2 X3 X4 X5
       have i₂ := eq2080 (M.op X0 X0) (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq2080 eq25363
    | exact resolve eq25363 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25363
  have eq26074 : ∀ X0 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) = (M.op (M.op X2 X3) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq25937 X0 x X2 X3 X4 X5
       have i₂ := eq3987 x (M.op X2 X3) (M.op X0 X0)
       grind)
    | exact superpose eq3987 eq25937
    | exact resolve eq25937 eq3987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987 eq25937
  have eq26131 : ∀ X0 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq26074 X0 X2 X3 X4 X5
       have i₂ := eq2080 X0 X0 X0
       grind)
    | exact superpose eq2080 eq26074
    | exact resolve eq26074 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080 eq26074
  have eq32930 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X3 (M.op X3 X3)) X3)))))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1316 X3 X4 X3 (M.op X3 (M.op X3 X3))
       have i₂ := eq25884 X1 X2 X0 (M.op (M.op X3 (M.op X3 X3)) X3)
       grind)
    | exact superpose eq25884 eq1316
    | exact resolve eq1316 eq25884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25884
  have eq32993 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1620 X1 X0 (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ X0))
       have i₂ := eq1316 (σ X0) (σ X1) (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq1316 eq1620
    | (have j0 := eq1620 X1 X0 x
       grind)
    | exact resolve eq1620 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq1620
  have eq33187 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32993 X0 X1
       have i₂ := eq3077 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq3077 eq32993
    | (have j0 := eq32993 X0 X1
       grind)
    | exact resolve eq32993 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32993
  have eq33229 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (M.op X3 X3)))))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32930 X0 X1 X2 X3 X4
       have i₂ := eq3077 X3 X3 X3
       grind)
    | exact superpose eq3077 eq32930
    | exact resolve eq32930 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077 eq32930
  have eq33399 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33187 X0 X1
       have j1 := eq13778 X0 X1
       grind)
    | (have r₁ := eq33187 X0 X1
       have r₂ := eq13778 X0 X1
       grind)
    | (have r₁ := eq33187 X0 X0
       have r₂ := eq13778 X0 X0
       grind)
    | exact resolve eq33187 eq13778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13778 eq33187
  have eq34386 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq33399 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33399
  have eq34687 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34386
  have eq35645 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34687
  have eq36736 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq35645 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35645
  have eq37009 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq36736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36736
  have eq37144 : ∀ X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq37009 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37009
  have eq37176 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq37144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37144
  have eq37868 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq37176 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37176
  have eq38073 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq37868 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37868
  have eq38125 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq38073 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38073
  have eq38519 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38125
  have eq38637 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq38519 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38519
  have eq39262 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq38637 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38637
  have eq39399 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq39262 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39262
  have eq39569 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq7438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39577 : ∀ X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq39399 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39399
  have eq39597 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq39569 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq39569
    | (have j0 := eq39569 (σ X0)
       grind)
    | exact resolve eq39569 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39598 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq39597 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39597
    | (have j0 := eq39597 X0
       grind)
    | exact resolve eq39597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39597
  have eq39601 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39598 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39598
    | (have j0 := eq39598 X0
       grind)
    | exact resolve eq39598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39598
  have eq40769 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39577 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39577
  have eq40968 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq40769 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40769
  have eq41428 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq40968 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40968
  have eq42065 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq41428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41428
  have eq42642 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq42065 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42065
  have eq42740 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq42642 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42642
  have eq43347 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq42740 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42740
  have eq43716 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43347 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43347
  have eq45145 : ∀ X2 X4 : G, (σ (k X4 X2)) = (M.op (σ X2) (σ X4)) ∨ (σ X2) = (M.op (σ X4) (σ X4)) := by
    intro X2 X4
    first
    | (have j0 := eq43716 X2 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43716
  have eq45997 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq45145 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45145
  have eq46912 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq45997 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45997
  have eq48152 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq46912 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46912
  have eq48336 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48152 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48152
  have eq48454 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq48336 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48336
  have eq48993 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq48454 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48454
  have eq49875 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq48993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48993
  have eq50071 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq49875 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49875
  have eq51228 : ∀ X0 X2 : G, (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq50071 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50071
  have eq51486 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq51228 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51228
  have eq51582 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq51486 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51486
  have eq51698 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq51582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51582
  have eq52427 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq51698 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51698
  have eq52604 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52427 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52427
  have eq53143 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq52604 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52604
  have eq53386 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq53143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53143
  have eq53920 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq53386 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53386
  have eq54117 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq53920 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53920
  have eq55018 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq54117 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54117
  have eq56083 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq55018 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55018
  have eq57608 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq56083 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56083
  have eq57897 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57608 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57608
  have eq58819 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57897 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57897
  have eq59133 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq58819 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58819
  have eq59504 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq59133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59133
  have eq59685 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq59504 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59504
  have eq59821 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq59685 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59685
  have eq60711 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq59821 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59821
  have eq60863 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq60711 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60711
  have eq61898 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq60863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60863
  have eq62098 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq61898 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61898
  have eq62941 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62098
  have eq63196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62941 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62941
  have eq63344 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq63196 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63196
  have eq63500 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq63344 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63344
  have eq64253 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq63500 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63500
  have eq64496 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64253
  have eq64583 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64496 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64496
  have eq64776 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64583 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64583
  have eq65582 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq64776 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64776
  have eq66234 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65582 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65582
  have eq66307 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66234 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66234
  have eq66606 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq66307 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66307
  have eq67693 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66606 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66606
  have eq68013 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67693 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67693
  have eq68148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68013 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68013
  have eq68894 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68148 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68148
  have eq69184 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq68894 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68894
  have eq69252 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq69184 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69184
  have eq70646 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69252 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69252
  have eq70989 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq70646 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70646
  have eq71932 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq70989 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70989
  have eq72441 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq71932 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71932
  have eq73764 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72441 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72441
  have eq73976 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73764 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73764
  have eq74124 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq73976 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73976
  have eq74309 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74124 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74124
  have eq75620 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74309
  have eq75936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75620
  have eq76157 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq75936 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75936
  have eq77476 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76157 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76157
  have eq77761 : ∀ X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq77476 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77476
  have eq77976 : ∀ X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq77761 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77761
  have eq78931 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77976 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77976
  have eq80177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78931 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78931
  have eq80315 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80177 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80177
  have eq81338 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq80315 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80315
  have eq81542 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq81338 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81338
  have eq82653 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq81542 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81542
  have eq84091 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82653 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82653
  have eq85579 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq84091 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84091
  have eq87246 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq85579 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85579
  have eq89053 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87246
  have eq89348 : ∀ X1 X2 : G, (σ (k X1 X2)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq89053 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89053
  have eq89575 : ∀ X2 X3 : G, (σ (k X2 X3)) = (M.op (σ X3) (σ X2)) ∨ (σ X3) = (M.op (σ X2) (σ X2)) := by
    intro X2 X3
    first
    | (have j0 := eq89348 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89348
  have eq90969 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89575 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89575
  have eq91264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq90969 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90969
  have eq91451 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq91264 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91264
  have eq92199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91451 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91451
  have eq92367 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq92199 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92199
  have eq92560 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq92367 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92367
  have eq93224 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92560
  have eq93527 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93224 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93224
  have eq94289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93527 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93527
  have eq94468 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94289 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94289
  have eq95109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94468 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94468
  have eq95282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95109 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95109
  have eq95444 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95282 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95282
  have eq95641 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95444
  have eq96410 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95641
  have eq96773 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq96410 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96410
  have eq97615 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq96773 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96773
  have eq97905 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq97615 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97615
  have eq98172 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq97905 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97905
  have eq98424 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq98172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98172
  have eq98701 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq98424 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98424
  have eq100110 : ∀ X0 X2 : G, (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq98701 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98701
  have eq100479 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq100110 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100110
  have eq100768 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq100479 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100479
  have eq101044 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq100768 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100768
  have eq101178 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq101044 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101044
  have eq101248 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq101178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101178
  have eq101266 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq101248 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101248
  have eq101382 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq101266 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101266
  have eq101545 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq101382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101382
  have eq103119 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq101545 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101545
  have eq103286 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq103119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103119
  have eq103423 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X3 X2)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq103286 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103286
  have eq104153 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103423
  have eq104510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq104153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104153
  have eq104655 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq104510 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104510
  have eq105049 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq104655 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104655
  have eq105275 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105049 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105049
  have eq105425 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq105275 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105275
  have eq105500 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105425
  have eq105524 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq105500 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105500
  have eq105784 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105524 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105524
  have eq106575 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X4 X3)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq105784 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105784
  have eq107406 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq106575 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106575
  have eq107426 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq107406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107406
  have eq107464 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107426 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq107426
    | (have j0 := eq107426 (τ X0) (τ X1)
       grind)
    | exact resolve eq107426 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107586 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107464 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107464
    | (have j0 := eq107464 X0 X1
       grind)
    | exact resolve eq107464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107464
  have eq107613 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107586 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq107586
    | (have j0 := eq107586 X0 X1
       grind)
    | exact resolve eq107586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107586
  have eq107621 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq107613 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq107613
    | (have j0 := eq107613 X0 X1
       grind)
    | exact resolve eq107613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107613
  have eq107627 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq107621 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107621
    | (have j0 := eq107621 X0 X1
       grind)
    | exact resolve eq107621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107621
  have eq107633 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107627 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq107627
    | (have j0 := eq107627 X0 X1
       grind)
    | exact resolve eq107627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107627
  have eq107679 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107426 X1 X0
       have i₂ := eq107633 X1 X0
       grind)
    | exact superpose eq107633 eq107426
    | (have j0 := eq107426 X1 X0
       have j1 := eq107633 (σ X1) (σ X0)
       grind)
    | exact resolve eq107426 eq107633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107633
  have eq109577 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq6609 eq13670
    | (have j0 := eq13670 X0
       have j1 := eq6609 X0
       grind)
    | exact resolve eq13670 eq6609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6609 eq13670
  have eq109578 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq109577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109577
  have eq109580 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq109578 eq478
    | (have j0 := eq478 X0
       have j1 := eq109578 X0
       grind)
    | exact resolve eq478 eq109578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq109733 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq109578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109578
  have eq109755 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq109580 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq109580
    | (have j0 := eq109580 X0
       grind)
    | exact resolve eq109580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109580
  have eq109780 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq109755 X0
       grind)
    | exact superpose eq109755 eq67
    | (have j1 := eq109755 X0
       grind)
    | exact resolve eq67 eq109755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq109781 : ∀ X0 : G, (k X0 (τ (τ (σ (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq109755 (σ X0)
       grind)
    | exact superpose eq109755 eq90
    | (have j1 := eq109755 (σ X0)
       grind)
    | exact resolve eq90 eq109755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq109755
  have eq109939 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109781 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq109781
    | (have j0 := eq109781 X0
       grind)
    | exact resolve eq109781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109781
  have eq109940 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109780 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109780
    | (have j0 := eq109780 X0
       grind)
    | exact resolve eq109780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109780
  have eq109960 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109939 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109939
    | (have j0 := eq109939 X0
       grind)
    | exact resolve eq109939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109939
  have eq109967 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109960 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq109960
    | (have j0 := eq109960 X0
       grind)
    | exact resolve eq109960 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109960
  have eq110836 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq109940 eq109967
    | (have j0 := eq109967 X0
       have j1 := eq109940 X0
       grind)
    | exact resolve eq109967 eq109940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109967
  have eq111106 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq110836 X0
       have j1 := eq39601 X0
       grind)
    | (have r₁ := eq110836 X0
       have r₂ := eq39601 X0
       grind)
    | exact resolve eq110836 eq39601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39601 eq110836
  have eq111156 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq111106 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq111106
    | (have j0 := eq111106 (τ X0)
       grind)
    | exact resolve eq111106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111227 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq957 (σ X0) (σ X0)
       have i₂ := eq111106 X0
       grind)
    | exact superpose eq111106 eq957
    | (have j1 := eq111106 X0
       grind)
    | exact resolve eq957 eq111106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111106
  have eq111329 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq7438 eq111156
    | (have j0 := eq111156 X0
       have j1 := eq7438 X0
       grind)
    | exact resolve eq111156 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7438 eq111156
  have eq111336 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq111329 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq111329
    | (have j0 := eq111329 X0
       grind)
    | exact resolve eq111329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111329
  have eq111337 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq111336 eq39569
    | (have j0 := eq39569 X0
       have j1 := eq111336 X0
       grind)
    | exact resolve eq39569 eq111336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39569
  have eq111359 : ∀ X0 : G, (k X0 (σ (σ (τ (τ X0))))) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq111336 (τ X0)
       grind)
    | exact superpose eq111336 eq48
    | (have j1 := eq111336 (τ X0)
       grind)
    | exact resolve eq48 eq111336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq111336
  have eq111530 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq111359 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq111359
    | (have j0 := eq111359 X0
       grind)
    | exact resolve eq111359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111359
  have eq111552 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq111530 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq111530
    | (have j0 := eq111530 X0
       grind)
    | exact resolve eq111530 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111530
  have eq111558 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq111552 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq111552
    | (have j0 := eq111552 X0
       grind)
    | exact resolve eq111552 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq111552
  have eq111561 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq109940 eq111558
    | (have j0 := eq111558 X0
       have j1 := eq109940 X0
       grind)
    | exact resolve eq111558 eq109940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109940 eq111558
  have eq111886 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111561 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq111561
    | (have j0 := eq111561 (σ X0)
       grind)
    | exact resolve eq111561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111561
  have eq112069 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111886 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq111886
    | (have j0 := eq111886 X0
       grind)
    | exact resolve eq111886 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111886
  have eq238014 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X3)) = (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1522 X2 x X3 X3 X3
       have i₂ := eq26131 X3 x X2 X0 X1
       grind)
    | exact superpose eq26131 eq1522
    | exact resolve eq1522 eq26131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522 eq26131
  have eq658340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq107679 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107679
  have eq658407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq658340 x y
       grind)
    | exact superpose eq658340 eq16
    | (have j1 := eq658340 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq658340 x y
       grind)
    | exact resolve eq16 eq658340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658340
  have eq658793 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq658407
  have eq659158 : (M.op y y) = (τ (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112069 y
       have i₂ := eq658793
       grind)
    | exact superpose eq658793 eq112069
    | (have j0 := eq112069 y
       grind)
    | exact resolve eq112069 eq658793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112069
  have eq659598 : x = (M.op y y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq659158
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq659158
    | exact resolve eq659158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659158
  have eq659599 : x = (M.op y y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq659598
  have eq659640 : (σ y) = (σ (k y y)) ∨ x = (M.op y y) := by grind
  clear eq659599
  have eq659653 : (σ y) = (σ (k y y)) ∨ x = (M.op y y) := by grind
  clear eq659640
  have eq659934 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq107426 y y
       have i₂ := eq659653
       grind)
    | exact superpose eq659653 eq107426
    | (have j0 := eq107426 y y
       grind)
    | exact resolve eq107426 eq659653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107426 eq659653
  have eq660050 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq659934
  have eq660127 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq658793 eq660050
    | exact resolve eq660050 eq658793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660050
  have eq660172 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq660127 eq658793
    | exact resolve eq658793 eq660127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658793
  have eq660403 : ∀ X0 X1 X2 : G, y = (M.op x (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 x))))) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33229 X0 X1 X2 y y
       have i₂ := eq660127
       grind)
    | exact superpose eq660127 eq33229
    | exact resolve eq33229 eq660127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33229 eq660127
  have eq660530 : y = (M.op x (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq660403 x x x
       have i₂ := eq238014 x x x x
       grind)
    | exact superpose eq238014 eq660403
    | exact resolve eq660403 eq238014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238014 eq660403
  have eq666591 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111337 (σ x)
       have i₂ := eq660172
       grind)
    | exact superpose eq660172 eq111337
    | (have j0 := eq111337 (σ x)
       grind)
    | exact resolve eq111337 eq660172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111337 eq660172
  have eq666863 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op y y) := by grind
  clear eq666591
  have eq666943 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq666863
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq666863
    | exact resolve eq666863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666863
  have eq667153 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq111227 y
       have i₂ := eq666943
       grind)
    | exact superpose eq666943 eq111227
    | (have j0 := eq111227 x
       grind)
    | exact resolve eq111227 eq666943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111227
  have eq667213 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq957 y y
       have i₂ := eq666943
       grind)
    | exact superpose eq666943 eq957
    | exact resolve eq957 eq666943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq741984 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq667153
       grind)
    | exact superpose eq667153 eq16
    | exact resolve eq16 eq667153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667153
  have eq742328 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq667213 eq741984
    | exact resolve eq741984 eq667213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667213 eq741984
  have eq742329 : x = (M.op x x) ∨ x = y := by grind
  clear eq742328
  have eq742436 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq742329 eq666943
    | exact resolve eq666943 eq742329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666943 eq742329
  have eq742824 : x = (M.op x x) := by grind
  clear eq742436
  have eq743005 : y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq660530
       have i₂ := eq742824
       grind)
    | exact superpose eq742824 eq660530
    | exact resolve eq660530 eq742824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660530
  have eq743066 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq109733 x
       have i₂ := eq742824
       grind)
    | exact superpose eq742824 eq109733
    | (have j0 := eq109733 x
       grind)
    | exact resolve eq109733 eq742824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109733
  have eq743361 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq743066
  have eq743472 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq743005
       have i₂ := eq742824
       grind)
    | exact superpose eq742824 eq743005
    | exact resolve eq743005 eq742824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743005
  have eq746439 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq743472
       grind)
    | exact superpose eq743472 eq10
    | exact resolve eq10 eq743472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743472
  have eq746661 : x = y ∨ x = y := by
    first
    | (have i₁ := eq746439
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq746439
    | exact resolve eq746439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746439
  have eq746662 : x = y := by grind
  clear eq746661
  have eq746715 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq746662
       grind)
    | exact superpose eq746662 eq16
    | exact resolve eq16 eq746662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746662
  have eq746739 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq746715
       have i₂ := eq742824
       grind)
    | exact superpose eq742824 eq746715
    | exact resolve eq746715 eq742824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742824 eq746715
  have eq746740 : False := by grind
  exact eq746740

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyy_pxx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq18
  have eq43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq43 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq46
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X2 X2))) = X2 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X1 X2) = X1 ∨ (M.op X2 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = X1 ∨ (M.op X0 X0) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq23 X0 x x X3
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq23 X1 x x X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq23 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq211 X0 X1 X2 X3
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq211
    | exact resolve eq211 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq493 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 (M.op X0 X1) x
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq208
    | exact resolve eq208 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (σ X0) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq210 (σ X0) X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq210
    | exact resolve eq210 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq210 X0 X0 X0
       grind)
    | exact superpose eq210 eq9
    | exact resolve eq9 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq208 (M.op x (M.op x x)) x
       have i₂ := eq210 x x x
       grind)
    | exact superpose eq210 eq208
    | exact resolve eq208 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq210
  have eq2065 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq71 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2066 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2065 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2273 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq2274 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2275 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2274 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq2274 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2274 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq2639 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq2275 (σ X0) X1
       grind)
    | exact superpose eq2275 eq30
    | (have j1 := eq2275 (σ X0) X1
       grind)
    | exact resolve eq30 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2275
  have eq2660 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2639 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq2639
    | (have j0 := eq2639 X0 X1
       grind)
    | exact resolve eq2639 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2681 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2660 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2660
    | (have j0 := eq2660 X0 X1
       grind)
    | exact resolve eq2660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660
  have eq2913 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 (M.op X0 X1) X1 X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq1339
    | exact resolve eq1339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2937 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 X2
       have i₂ := eq1339 X2 X0 X1
       grind)
    | exact superpose eq1339 eq113
    | exact resolve eq113 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2942 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1363 X2 X3
       have i₂ := eq1339 X2 X0 X1
       grind)
    | exact superpose eq1339 eq1363
    | exact resolve eq1363 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq2959 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq1339 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq1339 eq9
    | exact resolve eq9 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2961 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2)))) ∨ (M.op X3 X2) = (k X3 X2) ∨ (M.op X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X2 X3 (M.op X2 X2)
       have i₂ := eq1339 (M.op X2 X2) X0 X1
       grind)
    | exact superpose eq1339 eq69
    | (have j0 := eq69 X2 X3 X2
       grind)
    | exact resolve eq69 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq2983 : ∀ X2 X3 : G, (M.op X2 X2) = (M.op X3 X2) ∨ (M.op X3 X2) = (k X3 X2) ∨ (M.op X3 X2) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq2961 x x X2 X3
       have i₂ := eq9 X2 x x
       grind)
    | exact superpose eq9 eq2961
    | (have j0 := eq2961 x x X2 X3
       grind)
    | exact resolve eq2961 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961
  have eq3161 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2937 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2)) X1
       have i₂ := eq23 X2 x x X0
       grind)
    | exact superpose eq23 eq2937
    | exact resolve eq2937 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3202 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2937 x x (σ (M.op X0 X0))
       have i₂ := eq162 X0 x x
       grind)
    | exact superpose eq162 eq2937
    | exact resolve eq2937 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq3695 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq120 X0 (M.op X1 X0) X2 X3
       have i₂ := eq1339 X0 X0 X1
       grind)
    | exact superpose eq1339 eq120
    | exact resolve eq120 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3713 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq120 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq120 eq120
    | exact resolve eq120 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3768 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3695 X0 X1 x x
       have i₂ := eq120 X0 X0 x x
       grind)
    | exact superpose eq120 eq3695
    | exact resolve eq3695 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq3695
  have eq5410 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq224 (M.op (M.op x x) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0))) x x
       have i₂ := eq194 X0 X1 x x X4
       grind)
    | exact superpose eq194 eq224
    | exact resolve eq224 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq5440 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq224 (M.op X1 (M.op X2 X3)) X0 X3 X2
       have i₂ := eq1339 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq1339 eq224
    | exact resolve eq224 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq1339
  have eq5544 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5440 X0 X1 X2 X3
       have i₂ := eq2913 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq2913 eq5440
    | exact resolve eq5440 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913 eq5440
  have eq5571 : ∀ X0 X1 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq5410 X0 X1 X4 X5 X6
       have i₂ := eq3713 (M.op X4 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq3713 eq5410
    | exact resolve eq5410 eq3713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5410
  have eq5659 : ∀ X0 X1 X5 X6 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq5571 X0 X1 x X5 X6
       have i₂ := eq493 X1 X0 x
       grind)
    | exact superpose eq493 eq5571
    | exact resolve eq5571 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq5571
  have eq6906 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2066 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq6919 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6906 X0 X1
       have j1 := eq2983 X1 X0
       grind)
    | (have r₁ := eq6906 x x
       have r₂ := eq2983 x x
       grind)
    | (have r₁ := eq6906 x x
       have r₂ := eq2983 x x
       grind)
    | (have r₁ := eq6906 (M.op x x) x
       have r₂ := eq2983 x (M.op x x)
       grind)
    | exact resolve eq6906 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983 eq6906
  have eq7156 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2942 (M.op X3 (M.op X0 X0)) (M.op (M.op x x) (M.op X3 X3)) X2 X1
       have i₂ := eq23 X3 x x X0
       grind)
    | exact superpose eq23 eq2942
    | exact resolve eq2942 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq8937 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op (M.op X1 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3161 X0 (M.op (M.op X1 X0) (M.op X0 X0)) x
       have i₂ := eq2942 X0 X1 (M.op X0 X0) x
       grind)
    | exact superpose eq2942 eq3161
    | exact resolve eq3161 eq2942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq9043 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8937 X0 X1
       have i₂ := eq3768 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact superpose eq3768 eq8937
    | exact resolve eq8937 eq3768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768 eq8937
  have eq9091 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9043 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9043
    | exact resolve eq9043 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9043
  have eq10586 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9091 (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) X0
       have i₂ := eq3161 X2 X0 X1
       grind)
    | exact superpose eq3161 eq9091
    | exact resolve eq9091 eq3161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161 eq9091
  have eq10858 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10586 X0 X1 X2
       have i₂ := eq3713 (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op X1 (M.op X2 X2)) (M.op X2 X0)
       grind)
    | exact superpose eq3713 eq10586
    | exact resolve eq10586 eq3713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10586
  have eq10888 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10858 X0 X1 X2
       have i₂ := eq5659 (M.op X1 (M.op X2 X2)) (M.op X2 X0) (M.op X2 X0) (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq5659 eq10858
    | exact resolve eq10858 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq10906 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10888 X0 X1 X2
       have i₂ := eq5544 (M.op X2 X0) X1 X2 X2
       grind)
    | exact superpose eq5544 eq10888
    | exact resolve eq10888 eq5544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5544 eq10888
  have eq10918 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10906 X0 X1 X2
       have i₂ := eq3713 (M.op X2 X0) X2 X0
       grind)
    | exact superpose eq3713 eq10906
    | exact resolve eq10906 eq3713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713 eq10906
  have eq10926 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10918 X0 X1 X2
       have i₂ := eq5659 X2 X0 X0 X2
       grind)
    | exact superpose eq5659 eq10918
    | exact resolve eq10918 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10918
  have eq10930 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10926 X0 X1 X2
       have i₂ := eq24 (M.op X1 (M.op X2 X2)) (M.op X2 X0)
       grind)
    | exact superpose eq24 eq10926
    | exact resolve eq10926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10926
  have eq10934 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq10930 X0 x X2
       have i₂ := eq7156 X2 X2 X0 x
       grind)
    | exact superpose eq7156 eq10930
    | exact resolve eq10930 eq7156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156 eq10930
  have eq57118 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (σ (M.op X0 X0)))) (M.op (σ (σ X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1277 (σ X0) X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq1277
    | exact resolve eq1277 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq959517 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2681 X0 (σ X1)
       grind)
    | exact superpose eq2681 eq15
    | (have j1 := eq2681 X0 (σ X1)
       grind)
    | exact resolve eq15 eq2681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681
  have eq959619 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq959517 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq959517
    | (have j0 := eq959517 X0 X1
       grind)
    | exact resolve eq959517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959517
  have eq976759 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10934 X3 X2
       have i₂ := eq5659 X2 X3 X0 X1
       grind)
    | exact superpose eq5659 eq10934
    | exact resolve eq10934 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659 eq10934
  have eq1196011 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq959619 x y
       grind)
    | exact superpose eq959619 eq16
    | (have j1 := eq959619 x y
       grind)
    | exact resolve eq16 eq959619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959619
  have eq1206175 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1196011
       have i₂ := eq6919 x y
       grind)
    | exact superpose eq6919 eq1196011
    | (have j1 := eq6919 x y
       grind)
    | exact resolve eq1196011 eq6919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919 eq1196011
  have eq1206182 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1206175
  have eq1218896 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) (M.op x x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq976759 X0 X1 x y
       have i₂ := eq1206182
       grind)
    | exact superpose eq1206182 eq976759
    | exact resolve eq976759 eq1206182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206182
  have eq1218904 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1218896 x x
       have i₂ := eq2959 x x x x
       grind)
    | exact superpose eq2959 eq1218896
    | exact resolve eq1218896 eq2959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2959 eq1218896
  have eq1231292 : ∀ X0 X1 : G, y = (M.op (M.op X0 (σ (σ (M.op X1 X1)))) (M.op (σ (σ X1)) (M.op x x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq57118 X1 X0 y
       have i₂ := eq1218904
       grind)
    | exact superpose eq1218904 eq57118
    | exact resolve eq57118 eq1218904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218904
  have eq1231806 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1231292 x x
       have i₂ := eq57118 x x x
       grind)
    | exact superpose eq57118 eq1231292
    | exact resolve eq1231292 eq57118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57118 eq1231292
  have eq1232682 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq976759 X0 X1 x y
       have i₂ := eq1231806
       grind)
    | exact superpose eq1231806 eq976759
    | exact resolve eq976759 eq1231806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976759
  have eq1232689 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1232682 x x
       have i₂ := eq2937 x x x
       grind)
    | exact superpose eq2937 eq1232682
    | exact resolve eq1232682 eq2937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937 eq1232682
  have eq1238205 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3202 y
       have i₂ := eq1232689
       grind)
    | exact superpose eq1232689 eq3202
    | exact resolve eq3202 eq1232689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202 eq1232689
  have eq1304649 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1238205
       grind)
    | exact superpose eq1238205 eq16
    | exact resolve eq16 eq1238205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238205
  have eq1305604 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1304649
       have i₂ := eq1231806
       grind)
    | exact superpose eq1231806 eq1304649
    | exact resolve eq1304649 eq1231806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231806 eq1304649
  have eq1305617 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq1305604
  have eq1305618 : x = y := by grind
  clear eq1305617
  have eq1305953 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1305618
       grind)
    | exact superpose eq1305618 eq16
    | exact resolve eq16 eq1305618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305618
  have eq1305956 : False := by grind
  exact eq1305956

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X2 X0) (M.op X0 X0))
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
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
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq100 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq100
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq207 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq51
    | exact resolve eq51 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X1) X1 X2 X1
       have i₂ := eq54 X1 X1
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq664 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq835 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 X2
       have i₂ := eq54 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq54 eq66
    | (have j0 := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq66 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq66 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq66 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq924 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X1 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq835 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq976 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq209 eq51
    | exact resolve eq51 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq993 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq207 eq976
    | exact resolve eq976 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq976
  have eq1262 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq993 eq212
    | exact resolve eq212 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq993
  have eq1430 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq530 X0 X0 X0
       grind)
    | exact superpose eq530 eq51
    | exact resolve eq51 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq530 X0 X0 X0
       grind)
    | exact superpose eq530 eq52
    | exact resolve eq52 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1441 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561 (M.op x (M.op x x)) x
       have i₂ := eq530 x x x
       grind)
    | exact superpose eq530 eq561
    | exact resolve eq561 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq1658 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq1430 X0
       grind)
    | exact superpose eq1430 eq473
    | exact resolve eq473 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1685 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1430 eq476
    | exact resolve eq476 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1697 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq476 eq1685
    | exact resolve eq1685 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq1731 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq1658
    | exact resolve eq1658 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1658
  have eq1781 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq1731 X0
       grind)
    | exact superpose eq1731 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq1731 X0
       grind)
    | exact resolve eq13 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq1851 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1801 (M.op x (M.op x x))
       have i₂ := eq530 x x x
       grind)
    | exact superpose eq530 eq1801
    | exact resolve eq1801 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq2139 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1431 eq476
    | exact resolve eq476 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq2151 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq476 eq2139
    | exact resolve eq2139 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq2139
  have eq5882 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq92
    | (have j0 := eq92 x
       grind)
    | exact resolve eq92 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5906 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5882
  have eq5914 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5906
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5906
    | exact resolve eq5906 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5906
  have eq5922 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5914
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5914 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5914
  have eq5927 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5922 eq50
    | exact resolve eq50 eq5922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5994 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq93
    | (have j0 := eq93 y
       grind)
    | exact resolve eq93 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq6017 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5994
  have eq6024 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6017
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq6017
    | exact resolve eq6017 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq6017
  have eq6034 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6024
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6024 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6024
  have eq6783 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556 (M.op X1 X1) X1 X2
       have i₂ := eq924 X1 X1
       grind)
    | exact superpose eq924 eq556
    | exact resolve eq556 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq924
  have eq6845 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k X0 (M.op X0 (M.op X0 X0)))) (k X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6783 X1 X1 X2
       have i₂ := eq54 X1 X1
       grind)
    | exact superpose eq54 eq6783
    | exact resolve eq6783 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq6927 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6845 X0 X1 X2
       have i₂ := eq1851 X0
       grind)
    | exact superpose eq1851 eq6845
    | exact resolve eq6845 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851 eq6845
  have eq7071 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6927 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq473 X0
       grind)
    | exact superpose eq473 eq6927
    | exact resolve eq6927 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927
  have eq18181 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6034 eq107
    | exact resolve eq107 eq6034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq6034
  have eq18247 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5922 eq108
    | exact resolve eq108 eq5922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5922
  have eq18324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18324
    | exact resolve eq18324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18324
  have eq18333 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18325
       have r₂ := eq28
       grind)
    | exact resolve eq18325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18325
  have eq18335 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18333
    | exact resolve eq18333 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18333
  have eq18337 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18335 eq5927
    | exact resolve eq5927 eq18335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5927
  have eq18339 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq18335
  have eq18437 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18339
    | exact resolve eq18339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18339
  have eq18438 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq18437
  have eq18439 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq18337
    | exact resolve eq18337 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18337
  have eq18967 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18438 eq58
    | exact resolve eq58 eq18438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18438
  have eq18981 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq18967
    | exact resolve eq18967 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18967
  have eq19932 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq18439
       grind)
    | exact superpose eq18439 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19933 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19932
  have eq19990 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18981
       grind)
    | exact superpose eq18981 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18981
  have eq19991 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19990
  have eq19993 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19991
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19991
    | exact resolve eq19991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19991
  have eq20005 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19993
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19993
    | exact resolve eq19993 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19993
  have eq20006 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20005
  have eq20050 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1731 x
       have i₂ := eq20006
       grind)
    | exact superpose eq20006 eq1731
    | exact resolve eq1731 eq20006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq20058 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x x
       have i₂ := eq20006
       grind)
    | exact superpose eq20006 eq54
    | exact resolve eq54 eq20006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20079 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1441 x x
       have i₂ := eq20006
       grind)
    | exact superpose eq20006 eq1441
    | exact resolve eq1441 eq20006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441 eq20006
  have eq20097 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20079
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20079
    | exact resolve eq20079 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20079
  have eq20106 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20058
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20058
    | exact resolve eq20058 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20058
  have eq20166 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7071 y x
       have i₂ := eq20050
       grind)
    | exact superpose eq20050 eq7071
    | exact resolve eq7071 eq20050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7071
  have eq20260 : (M.op x y) = (M.op y (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20097 eq1262
    | exact resolve eq1262 eq20097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq20097
  have eq20764 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq473 x
       have i₂ := eq19933
       grind)
    | exact superpose eq19933 eq473
    | exact resolve eq473 eq19933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20823 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq20848 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20764
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20764
    | exact resolve eq20764 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20764
  have eq26168 : (M.op x y) = (M.op y (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20260
       have i₂ := eq20166
       grind)
    | exact superpose eq20166 eq20260
    | exact resolve eq20260 eq20166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20166 eq20260
  have eq26214 : (M.op x y) = (M.op y (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26168
  have eq32780 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18181
       have i₂ := eq20106
       grind)
    | exact superpose eq20106 eq18181
    | exact resolve eq18181 eq20106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20106
  have eq32835 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32780
  have eq32848 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32835
    | exact resolve eq32835 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32835
  have eq33029 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18247
       have i₂ := eq19933
       grind)
    | exact superpose eq19933 eq18247
    | exact resolve eq18247 eq19933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18247 eq19933
  have eq33098 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33029
       have r₂ := eq20823
       grind)
    | exact resolve eq33029 eq20823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33029
  have eq33108 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33098
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33098
    | exact resolve eq33098 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33098
  have eq33236 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33108 eq54
    | exact resolve eq54 eq33108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33108
  have eq33288 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq33236
    | exact resolve eq33236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33236
  have eq33592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33288 eq32848
    | exact resolve eq32848 eq33288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32848 eq33288
  have eq33683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33592
  have eq33710 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33683
       have r₂ := eq28
       grind)
    | exact resolve eq33683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33683
  have eq33884 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26214
       have i₂ := eq33710
       grind)
    | exact superpose eq33710 eq26214
    | exact resolve eq26214 eq33710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26214 eq33710
  have eq33980 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33884
  have eq35191 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20050
       have i₂ := eq33980
       grind)
    | exact superpose eq33980 eq20050
    | exact resolve eq20050 eq33980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20050 eq33980
  have eq35249 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq35191
  have eq35285 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35249 eq28
    | exact resolve eq28 eq35249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35325 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35249 eq2151
    | exact resolve eq2151 eq35249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35332 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq35325
    | exact resolve eq35325 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35325
  have eq35511 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35332 eq1801
    | exact resolve eq1801 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35737 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35249 eq35511
    | exact resolve eq35511 eq35249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35249 eq35511
  have eq35750 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq35737
  have eq35761 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35750 eq58
    | exact resolve eq58 eq35750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq35762 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35750 eq113
    | exact resolve eq113 eq35750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35750
  have eq35784 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq35762
  have eq35795 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq35784
       have r₂ := eq35285
       grind)
    | exact resolve eq35784 eq35285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35285 eq35784
  have eq35796 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq35761
    | exact resolve eq35761 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35761
  have eq35815 : y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  have eq35865 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54 x x
       have i₂ := eq35795
       grind)
    | exact superpose eq35795 eq54
    | exact resolve eq54 eq35795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq35795
  have eq35930 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35865
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35865
    | exact resolve eq35865 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35865
  have eq35951 : x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35815
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35815
    | exact resolve eq35815 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35815
  have eq35952 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq35951
  have eq36456 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18181
       have i₂ := eq35930
       grind)
    | exact superpose eq35930 eq18181
    | exact resolve eq18181 eq35930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18181 eq35930
  have eq36561 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq36456
  have eq36588 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq36561
    | exact resolve eq36561 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36561
  have eq36758 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35796
       have i₂ := eq35952
       grind)
    | exact superpose eq35952 eq35796
    | exact resolve eq35796 eq35952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35796 eq35952
  have eq36763 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq36758
  have eq36926 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36763 eq20848
    | exact resolve eq20848 eq36763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20848
  have eq36951 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq36926
  have eq36978 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36951
       have r₂ := eq20823
       grind)
    | exact resolve eq36951 eq20823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20823 eq36951
  have eq37045 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36978
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36978
    | exact resolve eq36978 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36978
  have eq37046 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq37045
  have eq37434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36588 eq35332
    | exact resolve eq35332 eq36588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35332 eq36588
  have eq37526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq37434
  have eq37548 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq37526
       have r₂ := eq28
       grind)
    | exact resolve eq37526 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37526
  have eq37703 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq37548
  have eq40107 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1801 x
       have i₂ := eq37046
       grind)
    | exact superpose eq37046 eq1801
    | exact resolve eq1801 eq37046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41069 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18439
       have i₂ := eq40107
       grind)
    | exact superpose eq40107 eq18439
    | exact resolve eq18439 eq40107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18439 eq40107
  have eq41092 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq41069
  have eq41106 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41092
       have r₂ := eq37703
       grind)
    | exact resolve eq41092 eq37703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41092
  have eq41741 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37046
       have i₂ := eq41106
       grind)
    | exact superpose eq41106 eq37046
    | exact resolve eq37046 eq41106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37046 eq41106
  have eq41836 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41741
  have eq41887 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq41836
       have r₂ := eq37703
       grind)
    | exact resolve eq41836 eq37703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41836
  have eq41908 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41887 eq28
    | exact resolve eq28 eq41887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41948 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41887 eq2151
    | exact resolve eq2151 eq41887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq41962 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq41948
    | exact resolve eq41948 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41948
  have eq42256 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41962 eq1801
    | exact resolve eq1801 eq41962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41962
  have eq42598 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41887 eq42256
    | exact resolve eq42256 eq41887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41887 eq42256
  have eq42617 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42598
  have eq43268 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42617 eq113
    | exact resolve eq113 eq42617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq42617
  have eq43292 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq43268
  have eq43306 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43292
       have r₂ := eq41908
       grind)
    | exact resolve eq43292 eq41908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41908 eq43292
  have eq43435 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq473 x
       have i₂ := eq43306
       grind)
    | exact superpose eq43306 eq473
    | exact resolve eq473 eq43306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq43306
  have eq43558 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43435
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43435
    | exact resolve eq43435 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43435
  have eq44743 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36763 eq43558
    | exact resolve eq43558 eq36763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36763 eq43558
  have eq44808 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq44743
  have eq44825 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq44808
       have r₂ := eq37703
       grind)
    | exact resolve eq44808 eq37703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37703 eq44808
  have eq44829 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44825
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44825
    | exact resolve eq44825 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44825
  have eq44830 : x = (M.op x y) := by grind
  clear eq44829
  have eq44835 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44830 eq21
    | exact resolve eq21 eq44830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq44921 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq44830 eq1697
    | exact resolve eq1697 eq44830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq44969 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44921
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44921
    | exact resolve eq44921 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq44921
  have eq45021 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44835
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44835
    | exact resolve eq44835 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44835
  have eq45024 : x = (M.op y y) := by
    first
    | exact superpose eq44830 eq44969
    | exact resolve eq44969 eq44830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44830 eq44969
  have eq45041 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45021 eq27
    | exact resolve eq27 eq45021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45230 : x = (k x y) := by
    first
    | (have i₁ := eq1801 y
       have i₂ := eq45024
       grind)
    | exact superpose eq45024 eq1801
    | exact resolve eq1801 eq45024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801 eq45024
  have eq45409 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq45230
       grind)
    | exact superpose eq45230 eq45
    | exact resolve eq45 eq45230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq45426 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq664 x y
       have i₂ := eq45230
       grind)
    | exact superpose eq45230 eq664
    | (have j0 := eq664 x y
       grind)
    | exact resolve eq664 eq45230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq45230
  have eq45429 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45426
  have eq45433 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45429
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45429
    | exact resolve eq45429 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45429
  have eq45445 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45021 eq45409
    | exact resolve eq45409 eq45021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45409
  have eq45447 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45021 eq45433
    | exact resolve eq45433 eq45021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45433
  have eq45459 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq45445
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45445
    | exact resolve eq45445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45445
  have eq45460 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45447
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq45447
    | exact resolve eq45447 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45447
  have eq45471 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45021 eq45459
    | exact resolve eq45459 eq45021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45459
  have eq45472 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq45460
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq45460
    | exact resolve eq45460 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq45460
  have eq45479 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq45472
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45472
    | exact resolve eq45472 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45472
  have eq45483 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq45479
    | exact resolve eq45479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45479
  have eq45487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45021 eq45483
    | exact resolve eq45483 eq45021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45021 eq45483
  have eq45490 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq45487
       have r₂ := eq28
       grind)
    | exact resolve eq45487 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45487
  have eq45554 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  have eq45702 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45471 eq45554
    | exact resolve eq45554 eq45471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45471 eq45554
  have eq45729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq45041 eq45702
    | exact resolve eq45702 eq45041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45702
  have eq45743 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq45729
       have r₂ := eq28
       grind)
    | exact resolve eq45729 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45729
  have eq45855 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45743 eq45041
    | exact resolve eq45041 eq45743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45041
  have eq45858 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45490 eq45855
    | exact resolve eq45855 eq45490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45490 eq45855
  have eq45920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45743 eq45858
    | exact resolve eq45858 eq45743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45743 eq45858
  have eq45969 : False := by grind
  exact eq45969

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq128 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq73 X1 X1
       grind)
    | exact superpose eq73 eq87
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq165 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq128 X0 X0 X0
       grind)
    | exact superpose eq128 eq128
    | exact resolve eq128 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq129 X2 X3
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq129
    | exact resolve eq129 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq66
    | exact resolve eq66 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq207 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq128 X2 X3 X2
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq128
    | exact resolve eq128 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X2 X2
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq87
    | exact resolve eq87 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq214 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq132 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq132 eq9
    | exact resolve eq9 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 (M.op X2 (M.op X0 X0)) (M.op x (M.op X2 X2)) X1
       have i₂ := eq128 X2 x X0
       grind)
    | exact superpose eq128 eq206
    | exact resolve eq206 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq205 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq128 X3 x X0
       grind)
    | exact superpose eq128 eq205
    | exact resolve eq205 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))) X3 X4
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X2 X2 X3 X4
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq69
    | exact resolve eq69 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq132 X0 X0 X1
       grind)
    | exact superpose eq132 eq69
    | exact resolve eq69 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq69 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq891
    | exact resolve eq891 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1803 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq165 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq205 X1 X2 X0 X4
       grind)
    | exact superpose eq205 eq165
    | exact resolve eq165 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1952 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1803 X0 X1 X2 X3 X4
       have i₂ := eq62 X4 X0
       grind)
    | exact superpose eq62 eq1803
    | exact resolve eq1803 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq2000 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1952 X0 X1 X2 X3 X4
       have i₂ := eq62 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq62 eq1952
    | exact resolve eq1952 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2023 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2000 X0 X1 X2 X3 X4
       have i₂ := eq205 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq205 eq2000
    | exact resolve eq2000 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2028 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2023 X0 x x X3 X4
       have i₂ := eq209 x x X0
       grind)
    | exact superpose eq209 eq2023
    | exact resolve eq2023 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2023
  have eq2047 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2028 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq165 X0 x X1
       grind)
    | exact superpose eq165 eq2028
    | exact resolve eq2028 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2115 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2047 X0 X1 X2
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq2047
    | exact resolve eq2047 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2131 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2115 X0 X1 X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq2115
    | exact resolve eq2115 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2115
  have eq3172 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq207 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq206 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq206 eq207
    | exact resolve eq207 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq3300 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3172 X0 X1 X2 X3
       have i₂ := eq2131 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2131 eq3172
    | exact resolve eq3172 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172
  have eq3356 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3300 X0 x X2 X3
       have i₂ := eq2028 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2028 eq3300
    | exact resolve eq3300 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq3300
  have eq4072 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq128 X1 x X0
       grind)
    | exact superpose eq128 eq214
    | exact resolve eq214 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq214
  have eq4198 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4072 X0 X1
       have i₂ := eq2131 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2131 eq4072
    | exact resolve eq4072 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4072
  have eq4239 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4198 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq165 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq165 eq4198
    | exact resolve eq4198 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq4330 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq4198 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq4198 eq205
    | exact resolve eq205 eq4198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4356 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4330 X0 X1 X2
       have i₂ := eq2131 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2131 eq4330
    | exact resolve eq4330 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330
  have eq4399 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4239 X0 X1
       have i₂ := eq2131 X0 X1 X1
       grind)
    | exact superpose eq2131 eq4239
    | exact resolve eq4239 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239
  have eq4437 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4399 X0 X1
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq4399
    | exact resolve eq4399 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq4399
  have eq4510 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4437 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq205 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq205 eq4437
    | exact resolve eq4437 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq4517 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4198 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq4437 X0 X1
       grind)
    | exact superpose eq4437 eq4198
    | exact resolve eq4198 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq4597 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4517 X0 X1
       have i₂ := eq2131 (M.op X1 X0) X0 X0
       grind)
    | exact superpose eq2131 eq4517
    | exact resolve eq4517 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517
  have eq4635 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4597 X0 X1
       have i₂ := eq3356 X0 X0 X1
       grind)
    | exact superpose eq3356 eq4597
    | exact resolve eq4597 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356 eq4597
  have eq4704 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4510 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq4437 X0 X2
       grind)
    | exact superpose eq4437 eq4510
    | exact resolve eq4510 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4437 eq4510
  have eq5124 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5124 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq5124 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq5124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5124
  have eq5169 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5125 (σ X0)
       grind)
    | exact superpose eq5125 eq15
    | exact resolve eq15 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5188 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5169 X0
       have i₂ := eq5125 X0
       grind)
    | exact superpose eq5125 eq5169
    | exact resolve eq5169 eq5125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5125 eq5169
  have eq5241 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq238 (σ X0) (σ X0) x
       have i₂ := eq5188 X0
       grind)
    | exact superpose eq5188 eq238
    | exact resolve eq238 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq5245 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq954 (σ X0) (σ X0)
       have i₂ := eq5188 X0
       grind)
    | exact superpose eq5188 eq954
    | exact resolve eq954 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5253 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq5188 X0
       grind)
    | exact superpose eq5188 eq9
    | exact resolve eq9 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5282 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5241 X0 x
       have i₂ := eq954 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq954 eq5241
    | exact resolve eq5241 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq5290 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5282 X0
       have i₂ := eq5188 (M.op X0 X0)
       grind)
    | exact superpose eq5188 eq5282
    | exact resolve eq5282 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5282
  have eq5293 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5290 X0
       have i₂ := eq2131 X0 X0 X0
       grind)
    | exact superpose eq2131 eq5290
    | exact resolve eq5290 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5290
  have eq5314 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq6284 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (σ (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5293 X2
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq5293
    | exact resolve eq5293 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq6861 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) = (M.op X2 (M.op (M.op X3 X2) (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0))) X2 X3
       have i₂ := eq5253 X0 (σ (M.op X0 X0)) X1
       grind)
    | exact superpose eq5253 eq69
    | exact resolve eq69 eq5253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq6925 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6861 X0 x X2 X3
       have i₂ := eq954 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq954 eq6861
    | exact resolve eq6861 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6861
  have eq6950 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (σ X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6925 X0 X2 X3
       have i₂ := eq5188 (M.op X0 X0)
       grind)
    | exact superpose eq5188 eq6925
    | exact resolve eq6925 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925
  have eq6969 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6950 X0 X2 X3
       have i₂ := eq2131 X0 X0 X0
       grind)
    | exact superpose eq2131 eq6950
    | exact resolve eq6950 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6950
  have eq7901 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4356 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4356 eq69
    | exact resolve eq69 eq4356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4356
  have eq7936 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7901 X0 X1 X2 X3
       have i₂ := eq2131 X3 X2 X2
       grind)
    | exact superpose eq2131 eq7901
    | exact resolve eq7901 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7901
  have eq8077 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq5314 X0 X1
       grind)
    | (have i₁ := eq9 X0 (σ X1) (σ X0)
       have i₂ := eq5314 X0 X1
       grind)
    | exact superpose eq5314 eq9
    | (have j1 := eq5314 X0 X1
       grind)
    | exact resolve eq9 eq5314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8080 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq5314 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq5314 X0 X1
       grind)
    | exact superpose eq5314 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq5314 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq5314 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq5314 X0 X1
       grind)
    | exact resolve eq13 eq5314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5314
  have eq8113 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8080 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8080
  have eq8114 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8113
  have eq8127 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8114 X0 X1
       have i₂ := eq5188 X1
       grind)
    | exact superpose eq5188 eq8114
    | (have j0 := eq8114 X0 X1
       grind)
    | exact resolve eq8114 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8114
  have eq8149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8127 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8127
    | (have j0 := eq8127 X0 X1
       grind)
    | exact resolve eq8127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq14325 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op X1 (M.op (M.op X2 X1) (τ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6284 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6284
    | exact resolve eq6284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6284
  have eq14835 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8149 (τ X0) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq8149
    | (have j0 := eq8149 (τ X0) X1
       grind)
    | exact resolve eq8149 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8149
  have eq14882 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14835 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14835
    | (have j0 := eq14835 X0 X1
       grind)
    | exact resolve eq14835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14835
  have eq14902 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14882 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14882
    | (have j0 := eq14882 X0 X1
       grind)
    | exact resolve eq14882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14882
  have eq16854 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X3 (M.op (M.op X4 X3) (σ X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6969 X2 X3 X4
       have i₂ := eq132 X2 X0 X1
       grind)
    | exact superpose eq132 eq6969
    | exact resolve eq6969 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq6969
  have eq22389 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq318 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq207 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq207 eq318
    | exact resolve eq318 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq318
  have eq22792 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22389 X0 X1 X2 X3 X4
       have i₂ := eq2131 X1 X0 X0
       grind)
    | exact superpose eq2131 eq22389
    | exact resolve eq22389 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22389
  have eq22885 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22792 X0 X1 X2 X3 X4
       have i₂ := eq7936 X3 X1 X0 X1
       grind)
    | exact superpose eq7936 eq22792
    | exact resolve eq22792 eq7936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7936 eq22792
  have eq22951 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8077 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8077
    | exact resolve eq8077 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8077
  have eq23130 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (σ X1)) (M.op X2 X2))) = X2 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22951 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq22951
    | (have j0 := eq22951 X0 X1 X2
       grind)
    | exact resolve eq22951 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq22951
  have eq39395 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4704 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq22885 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq22885 eq4704
    | exact resolve eq4704 eq22885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704 eq22885
  have eq46007 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4635 X0 X1
       have i₂ := eq898 X0 X1 X0
       grind)
    | exact superpose eq898 eq4635
    | exact resolve eq4635 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4635
  have eq136854 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq888 X0 X1 x X3 X4
       have i₂ := eq954 (M.op X1 (M.op X0 X1)) x
       grind)
    | exact superpose eq954 eq888
    | exact resolve eq888 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq136855 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq136854 X0 X1 X3 X4
       have i₂ := eq2131 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq2131 eq136854
    | exact resolve eq136854 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq136854
  have eq136856 : ∀ X0 X1 X3 X4 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq136855 X0 X1 X3 X4
       have i₂ := eq898 X1 X0 X1
       grind)
    | exact superpose eq898 eq136855
    | exact resolve eq136855 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136855
  have eq137408 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46007 X3 X2
       have i₂ := eq136856 X2 X3 X0 X1
       grind)
    | exact superpose eq136856 eq46007
    | exact resolve eq46007 eq136856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46007 eq136856
  have eq144016 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14902 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14902
  have eq156222 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ X0) (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23130 X1 X0 (M.op X1 (σ X0))
       have i₂ := eq898 (M.op X1 (σ X0)) X1 (σ X0)
       grind)
    | exact superpose eq898 eq23130
    | (have j0 := eq23130 X1 X0 x
       grind)
    | exact resolve eq23130 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq23130
  have eq156661 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156222 X0 X1
       have i₂ := eq137408 (σ X0) X1 X1 (σ X0)
       grind)
    | exact superpose eq137408 eq156222
    | (have j0 := eq156222 X0 X1
       grind)
    | exact resolve eq156222 eq137408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137408 eq156222
  have eq156764 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156661 X0 X1
       have i₂ := eq5188 X0
       grind)
    | exact superpose eq5188 eq156661
    | (have j0 := eq156661 X0 X1
       grind)
    | exact resolve eq156661 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156661
  have eq156825 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq156764 X0 X1
       have j1 := eq144016 X1 X0
       grind)
    | (have r₁ := eq156764 X1 X0
       have r₂ := eq144016 X0 X1
       grind)
    | (have r₁ := eq156764 X1 (σ (M.op X1 X1))
       have r₂ := eq144016 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq156764 eq144016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144016 eq156764
  have eq156872 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156825 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq156825
    | exact resolve eq156825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156825
  have eq157004 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq156872 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq156872
    | (have j0 := eq156872 (σ X1) (σ X0)
       grind)
    | exact resolve eq156872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157562 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq157004 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157004
  have eq159028 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq157562 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157562
  have eq161230 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq159028 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159028
  have eq163550 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq161230 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161230
  have eq164142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq163550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163550
  have eq164267 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq164142 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164142
  have eq166326 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq164267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164267
  have eq166567 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq166326 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166326
  have eq167661 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq166567 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166567
  have eq167941 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq167661 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167661
  have eq168063 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq167941 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167941
  have eq170240 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq168063 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168063
  have eq170846 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq170240 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170240
  have eq171045 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq170846 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170846
  have eq177169 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq171045 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171045
  have eq178256 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq177169 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177169
  have eq178520 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq178256 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178256
  have eq179601 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq178520 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178520
  have eq183226 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq179601 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179601
  have eq184610 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq183226 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183226
  have eq186824 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) X0)) = (σ (M.op X1 (M.op (M.op X2 X1) (τ X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16854 X1 X2 (τ X0) X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16854
    | exact resolve eq16854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16854
  have eq187670 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq184610 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184610
  have eq190753 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq187670 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187670
  have eq193396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190753 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190753
  have eq193907 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193396 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193396
  have eq194855 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193907 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193907
  have eq196171 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq194855 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194855
  have eq196455 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196171 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196171
  have eq196567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196455 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196455
  have eq198335 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq196567 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196567
  have eq200367 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq198335 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198335
  have eq200825 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200367 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200367
  have eq202037 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200825 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200825
  have eq203103 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq202037 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202037
  have eq205113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq203103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203103
  have eq207430 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq205113 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205113
  have eq208101 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq207430 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207430
  have eq211681 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq208101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208101
  have eq214096 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq211681 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211681
  have eq214793 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq214096 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214096
  have eq216031 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq214793 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214793
  have eq218347 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq216031 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216031
  have eq218554 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq218347 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218347
  have eq220307 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq218554 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218554
  have eq220779 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq220307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220307
  have eq223504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq220779 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220779
  have eq223729 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq223504 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223504
  have eq225067 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq223729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223729
  have eq225363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq225067 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225067
  have eq225502 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq225363 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225363
  have eq227539 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq225502 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225502
  have eq230720 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq227539 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227539
  have eq231254 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq230720 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230720
  have eq233678 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq231254 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231254
  have eq234868 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq233678 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233678
  have eq236659 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq234868 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234868
  have eq238358 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq236659 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236659
  have eq241049 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq238358 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238358
  have eq242965 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq241049 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241049
  have eq244703 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq242965 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242965
  have eq247471 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq244703 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244703
  have eq249496 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq247471 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247471
  have eq250813 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq249496 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249496
  have eq253687 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq250813 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250813
  have eq254368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253687
  have eq254553 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq254368 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254368
  have eq255694 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq254553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254553
  have eq256009 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq255694 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255694
  have eq257491 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq256009 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256009
  have eq262640 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq257491 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257491
  have eq264815 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq262640 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262640
  have eq267643 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq264815 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264815
  have eq270307 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq267643 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267643
  have eq270701 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq270307 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270307
  have eq276453 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq270701 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270701
  have eq279023 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq276453 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276453
  have eq283398 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq279023 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279023
  have eq285055 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq283398 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283398
  have eq286978 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq285055 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285055
  have eq291897 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq286978 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286978
  have eq293297 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq291897 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291897
  have eq294891 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq293297 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293297
  have eq296443 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq294891 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294891
  have eq299773 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq296443 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296443
  have eq301132 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq299773 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299773
  have eq303305 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq301132 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301132
  have eq304658 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq303305 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303305
  have eq305891 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq304658 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304658
  have eq307966 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq305891 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305891
  have eq308370 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq307966 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307966
  have eq309899 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq308370 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308370
  have eq310657 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq309899 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309899
  have eq312372 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq310657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310657
  have eq314991 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq312372 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312372
  have eq315296 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq314991 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314991
  have eq316611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq315296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315296
  have eq318701 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq316611 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316611
  have eq322183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq318701 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318701
  have eq325501 : ∀ X2 X4 : G, (M.op (σ X4) (σ X2)) = (σ (k X4 X2)) ∨ (σ X4) = (M.op (σ X4) (σ X2)) := by
    intro X2 X4
    first
    | (have j0 := eq322183 X4 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322183
  have eq327525 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq325501 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325501
  have eq330043 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq327525 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327525
  have eq332899 : ∀ X3 X4 : G, (σ (k X4 X3)) = (M.op (σ X4) (σ X3)) ∨ (σ X4) = (M.op (σ X4) (σ X3)) := by
    intro X3 X4
    first
    | (have j0 := eq330043 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330043
  have eq334337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332899 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332899
  have eq334571 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq334337 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334337
  have eq337940 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq334571 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334571
  have eq338478 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq337940 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337940
  have eq338689 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq338478 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338478
  have eq341582 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq338689 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338689
  have eq342195 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq341582 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341582
  have eq351001 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq342195 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342195
  have eq352422 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq351001 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351001
  have eq355976 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq352422 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352422
  have eq357915 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (σ (M.op X0 (M.op (M.op X1 X0) (τ (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq889 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq186824 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1 (M.op X4 X5) X3
       grind)
    | exact superpose eq186824 eq889
    | exact resolve eq889 eq186824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq186824
  have eq358414 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (σ (M.op X0 (M.op (M.op X1 X0) (τ (M.op X5 X6)))))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq357915 X0 X1 x x x X5 X6
       have i₂ := eq39395 X6 x x x X5
       grind)
    | exact superpose eq39395 eq357915
    | exact resolve eq357915 eq39395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39395 eq357915
  have eq358776 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq355976 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355976
  have eq360547 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq358776 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358776
  have eq363371 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq360547 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360547
  have eq364814 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq363371 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363371
  have eq365638 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq364814 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364814
  have eq370835 : ∀ X3 X4 : G, (σ (k X4 X3)) = (M.op (σ X4) (σ X3)) ∨ (σ X4) = (M.op (σ X4) (σ X3)) := by
    intro X3 X4
    first
    | (have j0 := eq365638 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365638
  have eq371977 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq370835 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370835
  have eq372177 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq371977 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371977
  have eq373378 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq372177 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372177
  have eq374123 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq373378 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373378
  have eq376683 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq374123 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374123
  have eq376928 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq376683 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376683
  have eq379426 : ∀ X3 X4 : G, (σ (k X4 X3)) = (M.op (σ X4) (σ X3)) ∨ (σ X4) = (M.op (σ X4) (σ X3)) := by
    intro X3 X4
    first
    | (have j0 := eq376928 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376928
  have eq380563 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq379426 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379426
  have eq380764 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq380563 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380563
  have eq381986 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq380764 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380764
  have eq382748 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq381986 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381986
  have eq384052 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq382748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382748
  have eq385347 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq384052 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384052
  have eq390962 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq385347 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385347
  have eq391599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq390962 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390962
  have eq394411 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq391599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391599
  have eq397854 : ∀ X4 X5 : G, (σ (k X5 X4)) = (M.op (σ X5) (σ X4)) ∨ (σ X5) = (M.op (σ X5) (σ X4)) := by
    intro X4 X5
    first
    | (have j0 := eq394411 X5 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394411
  have eq399382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq397854 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397854
  have eq399622 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq399382 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399382
  have eq402972 : ∀ X4 X5 : G, (M.op (σ X4) (σ X5)) = (σ (k X4 X5)) ∨ (σ X4) = (M.op (σ X4) (σ X5)) := by
    intro X4 X5
    first
    | (have j0 := eq399622 X4 X5
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399622
  have eq403758 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq402972 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402972
  have eq405156 : ∀ X2 X3 : G, (σ (k X3 X2)) = (M.op (σ X3) (σ X2)) ∨ (σ X3) = (M.op (σ X3) (σ X2)) := by
    intro X2 X3
    first
    | (have j0 := eq403758 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403758
  have eq406016 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq405156 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405156
  have eq408212 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq406016 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406016
  have eq411281 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq408212 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408212
  have eq411631 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq411281 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411281
  have eq414073 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq411631 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411631
  have eq416091 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq414073 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414073
  have eq416486 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq416091 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416091
  have eq417710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq416486 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416486
  have eq418224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq417710 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417710
  have eq419421 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq418224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418224
  have eq423114 : ∀ X4 X5 : G, (σ (k X5 X4)) = (M.op (σ X5) (σ X4)) ∨ (σ X5) = (M.op (σ X5) (σ X4)) := by
    intro X4 X5
    first
    | (have j0 := eq419421 X5 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419421
  have eq424217 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq423114 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423114
  have eq424806 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq424217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424217
  have eq425014 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq424806 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424806
  have eq426616 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq425014 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425014
  have eq429405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq426616 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426616
  have eq430617 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq429405 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429405
  have eq432933 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq430617 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430617
  have eq434150 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq432933 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432933
  have eq436376 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq434150 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434150
  have eq436805 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq436376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436376
  have eq438806 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq436805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436805
  have eq439581 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq438806 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438806
  have eq441398 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq439581 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439581
  have eq442782 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq441398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441398
  have eq443034 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq442782 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442782
  have eq444455 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq443034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443034
  have eq446174 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq444455 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444455
  have eq447249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq446174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446174
  have eq447949 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq447249 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447249
  have eq450079 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq447949 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447949
  have eq450662 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq450079 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450079
  have eq454095 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq450662 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450662
  have eq455061 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq454095 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454095
  have eq455885 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq455061 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455061
  have eq457114 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq455885 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455885
  have eq459135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq457114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457114
  have eq459592 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq459135 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459135
  have eq463190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq459592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459592
  have eq466226 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq463190 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463190
  have eq467187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq466226 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466226
  have eq467852 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq467187 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467187
  have eq469719 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq467852 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467852
  have eq471519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq469719 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469719
  have eq471958 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq471519 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471519
  have eq473931 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq471958 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471958
  have eq477854 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq473931 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473931
  have eq478529 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq477854 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477854
  have eq481695 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq478529 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478529
  have eq491062 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq481695 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481695
  have eq492109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq491062 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491062
  have eq495382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq492109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492109
  have eq497693 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq495382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495382
  have eq499751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq497693 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497693
  have eq501474 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq499751 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499751
  have eq504236 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq501474 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501474
  have eq505705 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq504236 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504236
  have eq508204 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq505705 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505705
  have eq510921 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq508204 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508204
  have eq512999 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq510921 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510921
  have eq513494 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq512999 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512999
  have eq514584 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq513494 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513494
  have eq515097 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq514584 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514584
  have eq519103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq515097 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515097
  have eq521936 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X2) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq519103 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519103
  have eq527381 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq521936 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521936
  have eq528172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq527381 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527381
  have eq529795 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq528172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528172
  have eq530289 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq529795 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529795
  have eq533398 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq530289 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530289
  have eq534599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq533398 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533398
  have eq535132 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq534599 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534599
  have eq536553 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq535132 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535132
  have eq539654 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq536553 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536553
  have eq541237 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq539654 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539654
  have eq543366 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq541237 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541237
  have eq543863 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq543366 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543366
  have eq545466 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq543863 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543863
  have eq545805 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq545466 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545466
  have eq547938 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq545805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545805
  have eq548190 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq547938 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547938
  have eq549637 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X3) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq548190 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548190
  have eq556640 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq549637 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549637
  have eq558530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq556640 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556640
  have eq561075 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X2) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq558530 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558530
  have eq566710 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561075 X1 X0
       have i₂ := eq156872 X1 X0
       grind)
    | exact superpose eq156872 eq561075
    | (have j0 := eq561075 X1 X0
       have j1 := eq156872 (σ X1) (σ X0)
       grind)
    | exact resolve eq561075 eq156872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156872 eq561075
  have eq792484 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq566710 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566710
  have eq792651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq792484 x y
       grind)
    | exact superpose eq792484 eq16
    | (have j1 := eq792484 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq792484 x y
       grind)
    | exact resolve eq16 eq792484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792484
  have eq793362 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq792651
  have eq794232 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq954 (σ y) (σ x)
       have i₂ := eq793362
       grind)
    | exact superpose eq793362 eq954
    | exact resolve eq954 eq793362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794533 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq794232
       have i₂ := eq5188 y
       grind)
    | exact superpose eq5188 eq794232
    | exact resolve eq794232 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188 eq794232
  have eq794582 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq793362 eq794533
    | exact resolve eq794533 eq793362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793362 eq794533
  have eq794726 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq794582
       grind)
    | exact superpose eq794582 eq10
    | exact resolve eq10 eq794582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794582
  have eq795146 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq794726
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq794726
    | exact resolve eq794726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794726
  have eq795615 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq954 y y
       have i₂ := eq795146
       grind)
    | exact superpose eq795146 eq954
    | exact resolve eq954 eq795146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq795146
  have eq795860 : x = (M.op x y) := by grind
  clear eq795615
  have eq796319 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq795860
       grind)
    | exact superpose eq795860 eq16
    | exact resolve eq16 eq795860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796561 : ∀ X0 X1 : G, (M.op y y) = (M.op x (σ (M.op X0 (M.op (M.op X1 X0) (τ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq358414 X0 X1 x y
       have i₂ := eq795860
       grind)
    | exact superpose eq795860 eq358414
    | exact resolve eq358414 eq795860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358414 eq795860
  have eq796593 : x = (M.op y y) := by
    first
    | (have i₁ := eq796561 x x
       have i₂ := eq14325 x x x
       grind)
    | exact superpose eq14325 eq796561
    | exact resolve eq796561 eq14325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14325 eq796561
  have eq796647 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5245 y
       have i₂ := eq796593
       grind)
    | exact superpose eq796593 eq5245
    | exact resolve eq5245 eq796593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245 eq796593
  have eq797268 : False := by grind
  exact eq797268

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  clear eq18
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X0 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X3
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq87 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq12
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq25 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq25
    | exact resolve eq25 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq87 X0
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq97 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq131 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 X0) X2 X3 X4
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X1 X1) X1 X2 X1
       have i₂ := eq25 X1 X1
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq154 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq154
    | exact resolve eq154 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq170 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq140 X0 X1 X2 X3 X4
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq140
    | exact resolve eq140 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 (M.op X0 X1) x
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq151
    | exact resolve eq151 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq636 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq153 X0 X0 X0
       grind)
    | exact superpose eq153 eq9
    | exact resolve eq9 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 (M.op x (M.op x x))
       have i₂ := eq153 x x x
       grind)
    | exact superpose eq153 eq99
    | exact resolve eq99 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 (M.op x (M.op x x)) x
       have i₂ := eq153 x x x
       grind)
    | exact superpose eq153 eq151
    | exact resolve eq151 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq647 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq647
    | exact resolve eq647 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq647
  have eq1234 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq636 (M.op X0 X1) X1 X0
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq636
    | exact resolve eq636 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1269 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X2
       have i₂ := eq636 X2 X0 X1
       grind)
    | exact superpose eq636 eq87
    | exact resolve eq87 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1272 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X2
       have i₂ := eq636 X2 X0 X1
       grind)
    | exact superpose eq636 eq99
    | exact resolve eq99 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1274 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq649 X2 X3
       have i₂ := eq636 X2 X0 X1
       grind)
    | exact superpose eq636 eq649
    | exact resolve eq649 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq1275 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op (M.op X1 X0) X2)) (M.op X2 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq651 X2
       have i₂ := eq636 X2 X0 X1
       grind)
    | exact superpose eq636 eq651
    | exact resolve eq651 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq1293 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq636 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq636 eq9
    | exact resolve eq9 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1269 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2)) X1
       have i₂ := eq24 X2 x x X0
       grind)
    | exact superpose eq24 eq1269
    | exact resolve eq1269 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1440 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1269 x x X1
       have i₂ := eq52 X1 x x X0
       grind)
    | (have i₁ := eq1269 X0 X1 x
       have i₂ := eq52 X0 X1 x (M.op X0 (M.op (M.op X1 X0) x))
       grind)
    | exact superpose eq52 eq1269
    | (have j1 := eq52 X1 X1 x X0
       grind)
    | exact resolve eq1269 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1440 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1511 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 (M.op X1 X0) X2 X3
       have i₂ := eq636 X0 X0 X1
       grind)
    | exact superpose eq636 eq92
    | exact resolve eq92 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1525 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq92 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1569 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1511 X0 X1 x x
       have i₂ := eq92 X0 X0 x x
       grind)
    | exact superpose eq92 eq1511
    | exact resolve eq1511 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1511
  have eq2174 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1272 x x X1
       have i₂ := eq52 X1 x x X0
       grind)
    | (have i₁ := eq1272 X0 X1 x
       have i₂ := eq52 X0 X1 x (M.op X0 (M.op (M.op X1 X0) x))
       grind)
    | exact superpose eq52 eq1272
    | (have j1 := eq52 X1 X1 x X0
       grind)
    | exact resolve eq1272 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1272
  have eq2194 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2174 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2174 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2174 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq3081 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq164 (M.op (M.op x x) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0))) x x
       have i₂ := eq139 X0 X1 x x X4
       grind)
    | exact superpose eq139 eq164
    | exact resolve eq164 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq3107 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq164 (M.op X1 (M.op X2 X3)) X0 X3 X2
       have i₂ := eq636 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq636 eq164
    | exact resolve eq164 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq636
  have eq3239 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3107 X0 X1 X2 X3
       have i₂ := eq1234 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq1234 eq3107
    | exact resolve eq3107 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107
  have eq3259 : ∀ X0 X1 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq3081 X0 X1 X4 X5 X6
       have i₂ := eq1525 (M.op X4 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq1525 eq3081
    | exact resolve eq3081 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq3323 : ∀ X0 X1 X5 X6 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq3259 X0 X1 x X5 X6
       have i₂ := eq181 X1 X0 x
       grind)
    | exact superpose eq181 eq3259
    | exact resolve eq3259 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3259
  have eq3402 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (k (M.op X0 X0) (M.op (M.op X2 (M.op (M.op X3 X2) X0)) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1275 X0 x (M.op X2 (M.op (M.op X3 X2) X0))
       have i₂ := eq1274 X2 X3 X0 x
       grind)
    | exact superpose eq1274 eq1275
    | exact resolve eq1275 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq3481 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (k (M.op X0 X0) (M.op (M.op (M.op X3 X2) X0) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3402 X0 X2 X3
       have i₂ := eq25 X2 (M.op (M.op X3 X2) X0)
       grind)
    | exact superpose eq25 eq3402
    | exact resolve eq3402 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402
  have eq3510 : ∀ X0 X2 X3 : G, (k (M.op X0 X0) X0) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3481 X0 X2 X3
       have i₂ := eq1274 X2 X3 X0 (M.op X3 X2)
       grind)
    | exact superpose eq1274 eq3481
    | exact resolve eq3481 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274 eq3481
  have eq3555 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq321 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq321
    | exact resolve eq321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq321
  have eq3569 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3555 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq3577 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3569 X0 X1
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq3569 X0 X1
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq3569 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq3569
  have eq3613 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (M.op X1 X2) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3577 (M.op (M.op X1 X0) (M.op x x)) (M.op (M.op X2 x) (M.op X0 (M.op X1 X0)))
       have i₂ := eq131 X0 X1 X2 x x
       grind)
    | exact superpose eq131 eq3577
    | exact resolve eq3577 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq3577
  have eq3644 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3613 X0 x x
       have i₂ := eq151 X0 (M.op x x)
       grind)
    | exact superpose eq151 eq3613
    | exact resolve eq3613 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613
  have eq3759 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3644 (σ X0)
       grind)
    | exact superpose eq3644 eq15
    | exact resolve eq15 eq3644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3770 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3759 X0
       have i₂ := eq3644 X0
       grind)
    | exact superpose eq3644 eq3759
    | exact resolve eq3759 eq3644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3644 eq3759
  have eq4159 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (σ X0) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 (σ X0) X1 X2
       have i₂ := eq3770 X0
       grind)
    | exact superpose eq3770 eq153
    | exact resolve eq153 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq4197 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1569 (σ X0) (σ X0)
       have i₂ := eq3770 X0
       grind)
    | exact superpose eq3770 eq1569
    | exact resolve eq1569 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5142 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq5322 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5142 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5142
    | (have j0 := eq5142 X0 X1
       grind)
    | exact resolve eq5142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq6046 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170 (M.op X1 (M.op X2 X2)) (M.op X2 X0) X3 X4 X0
       have i₂ := eq1415 X2 X0 X1
       grind)
    | exact superpose eq1415 eq170
    | exact resolve eq170 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq1415
  have eq6348 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6046 X0 X1 X2 X3 X4
       have i₂ := eq1234 (M.op X2 X0) (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq1234 eq6046
    | exact resolve eq6046 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234 eq6046
  have eq6469 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X0)) X0) = (M.op X2 (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq6348 X0 x X2 X3 X4
       have i₂ := eq3239 (M.op X2 X0) x X2 X2
       grind)
    | exact superpose eq3239 eq6348
    | exact resolve eq6348 eq3239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239 eq6348
  have eq6534 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X0)) X0) = (M.op X2 (M.op X0 (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq6469 X0 X2 X3 X4
       have i₂ := eq1525 (M.op X2 X0) X2 X0
       grind)
    | exact superpose eq1525 eq6469
    | exact resolve eq6469 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq6469
  have eq6564 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X0)) X0) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq6534 X0 X2 X3 X4
       have i₂ := eq3323 X2 X0 X0 X2
       grind)
    | exact superpose eq3323 eq6534
    | exact resolve eq6534 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6570 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq6564 X0 X2 x x
       have i₂ := eq151 X0 (M.op x x)
       grind)
    | exact superpose eq151 eq6564
    | exact resolve eq6564 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq6564
  have eq7495 : ∀ X0 X1 : G, (k (M.op X1 X1) X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3510 X1 (M.op X0 (M.op X0 X0)) (M.op (M.op x x) (M.op X0 (M.op X0 X0)))
       have i₂ := eq143 X0 x x
       grind)
    | exact superpose eq143 eq3510
    | exact resolve eq3510 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq3510
  have eq31403 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq2194 X1 (σ X0)
       grind)
    | exact superpose eq2194 eq31
    | (have j1 := eq2194 X1 (σ X0)
       grind)
    | exact resolve eq31 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2194
  have eq31478 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31403 X0 X1
       have i₂ := eq3770 X0
       grind)
    | exact superpose eq3770 eq31403
    | (have j0 := eq31403 X0 X1
       grind)
    | exact resolve eq31403 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31403
  have eq31587 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31478 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31478
    | (have j0 := eq31478 X0 X1
       grind)
    | exact resolve eq31478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq117963 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (σ (M.op X0 X0)))) (M.op (σ (σ X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4159 (σ X0) X1 X2
       have i₂ := eq3770 X0
       grind)
    | exact superpose eq3770 eq4159
    | exact resolve eq4159 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159
  have eq169517 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6570 X3 X2
       have i₂ := eq3323 X2 X3 X0 X1
       grind)
    | exact superpose eq3323 eq6570
    | exact resolve eq6570 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323 eq6570
  have eq192008 : ∀ X0 X1 : G, (k X0 X1) = (M.op (M.op X1 X0) X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7495 X1 X1
       have i₂ := eq5322 X0 X1
       grind)
    | (have i₁ := eq7495 X0 X1
       have i₂ := eq5322 (M.op X0 X1) X1
       grind)
    | exact superpose eq5322 eq7495
    | (have j1 := eq5322 X0 X1
       grind)
    | exact resolve eq7495 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322 eq7495
  have eq192488 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq192008 X0 X1
       have i₂ := eq1569 X0 X1
       grind)
    | exact superpose eq1569 eq192008
    | (have j0 := eq192008 X0 X1
       grind)
    | exact resolve eq192008 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq192008
  have eq192606 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192488 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq192488 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq192488 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192488
  have eq1227313 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq31587 X0 (σ X1)
       grind)
    | exact superpose eq31587 eq15
    | (have j1 := eq31587 X0 (σ X1)
       grind)
    | exact resolve eq15 eq31587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31587
  have eq1227486 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1227313 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1227313
    | (have j0 := eq1227313 X0 X1
       grind)
    | exact resolve eq1227313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227313
  have eq1834293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1227486 x y
       grind)
    | exact superpose eq1227486 eq16
    | (have j1 := eq1227486 x y
       grind)
    | exact resolve eq16 eq1227486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227486
  have eq1835858 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq192606 x y
       grind)
    | (have r₁ := eq1834293
       have r₂ := eq192606 x y
       grind)
    | exact resolve eq1834293 eq192606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192606 eq1834293
  have eq1839595 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1454 y x
       have i₂ := eq1835858
       grind)
    | exact superpose eq1835858 eq1454
    | (have j0 := eq1454 y x
       grind)
    | exact resolve eq1454 eq1835858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq1835858
  have eq1845847 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) (M.op x x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq169517 X0 X1 x y
       have i₂ := eq1839595
       grind)
    | exact superpose eq1839595 eq169517
    | exact resolve eq169517 eq1839595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839595
  have eq1845867 : (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1845847 x x
       have i₂ := eq1293 x x x x
       grind)
    | exact superpose eq1293 eq1845847
    | exact resolve eq1845847 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq1845847
  have eq1854283 : ∀ X0 X1 : G, y = (M.op (M.op X0 (σ (σ (M.op X1 X1)))) (M.op (σ (σ X1)) (M.op x x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq117963 X1 X0 y
       have i₂ := eq1845867
       grind)
    | exact superpose eq1845867 eq117963
    | exact resolve eq117963 eq1845867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845867
  have eq1855046 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1854283 x x
       have i₂ := eq117963 x x x
       grind)
    | exact superpose eq117963 eq1854283
    | exact resolve eq1854283 eq117963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117963 eq1854283
  have eq1862228 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq169517 X0 X1 x y
       have i₂ := eq1855046
       grind)
    | exact superpose eq1855046 eq169517
    | exact resolve eq169517 eq1855046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169517
  have eq1862246 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1862228 x x
       have i₂ := eq1269 x x x
       grind)
    | exact superpose eq1269 eq1862228
    | exact resolve eq1862228 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269 eq1862228
  have eq1870438 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4197 y
       have i₂ := eq1862246
       grind)
    | exact superpose eq1862246 eq4197
    | exact resolve eq4197 eq1862246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4197 eq1862246
  have eq1954219 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1870438
       grind)
    | exact superpose eq1870438 eq16
    | exact resolve eq16 eq1870438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870438
  have eq1956962 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1954219
       have i₂ := eq1855046
       grind)
    | exact superpose eq1855046 eq1954219
    | exact resolve eq1954219 eq1855046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855046 eq1954219
  have eq1956969 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq1956962
  have eq1956970 : x = y := by grind
  clear eq1956969
  have eq1961556 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1956970
       grind)
    | exact superpose eq1956970 eq16
    | exact resolve eq16 eq1956970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956970
  have eq1961560 : False := by grind
  exact eq1961560

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X0 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X3
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq12
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq87 X0
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq97 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq139 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq154 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq154
    | exact resolve eq154 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 (M.op X0 X1) x
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq151
    | exact resolve eq151 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq153 X0 X0 X0
       grind)
    | exact superpose eq153 eq9
    | exact resolve eq9 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 (M.op x (M.op x x)) x
       have i₂ := eq153 x x x
       grind)
    | exact superpose eq153 eq151
    | exact resolve eq151 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq153
  have eq599 : ∀ X0 X1 X2 X3 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X2 (M.op (M.op X3 X2) X0)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq52 X0 X2 X3 (τ X1)
       grind)
    | exact superpose eq52 eq19
    | (have j1 := eq52 X0 X2 X3 (τ X1)
       grind)
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1064 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 (M.op X0 X1) X1 X0
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq510
    | exact resolve eq510 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X2
       have i₂ := eq510 X2 X0 X1
       grind)
    | exact superpose eq510 eq87
    | exact resolve eq87 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1102 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X2
       have i₂ := eq510 X2 X0 X1
       grind)
    | exact superpose eq510 eq99
    | exact resolve eq99 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq522 X2 X3
       have i₂ := eq510 X2 X0 X1
       grind)
    | exact superpose eq510 eq522
    | exact resolve eq522 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq1123 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq510 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq510 eq9
    | exact resolve eq9 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1099 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2)) X1
       have i₂ := eq24 X2 x x X0
       grind)
    | exact superpose eq24 eq1099
    | exact resolve eq1099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1252 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1099 x x X1
       have i₂ := eq52 X1 x x X0
       grind)
    | (have i₁ := eq1099 X0 X1 x
       have i₂ := eq52 X0 X1 x (M.op X0 (M.op (M.op X1 X0) x))
       grind)
    | exact superpose eq52 eq1099
    | (have j1 := eq52 X1 X1 x X0
       grind)
    | exact resolve eq1099 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1527 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 (M.op X1 X0) X2 X3
       have i₂ := eq510 X0 X0 X1
       grind)
    | exact superpose eq510 eq92
    | exact resolve eq92 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq92 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1587 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1527 X0 X1 x x
       have i₂ := eq92 X0 X0 x x
       grind)
    | exact superpose eq92 eq1527
    | exact resolve eq1527 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1527
  have eq1901 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 x x X1
       have i₂ := eq52 X1 x x X0
       grind)
    | (have i₁ := eq1102 X0 X1 x
       have i₂ := eq52 X0 X1 x (M.op X0 (M.op (M.op X1 X0) x))
       grind)
    | exact superpose eq52 eq1102
    | (have j1 := eq52 X1 X1 x X0
       grind)
    | exact resolve eq1102 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1918 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1901 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1901 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1901 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq2141 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1104 (M.op X3 (M.op X0 X0)) (M.op (M.op x x) (M.op X3 X3)) X2 X1
       have i₂ := eq24 X3 x x X0
       grind)
    | exact superpose eq24 eq1104
    | exact resolve eq1104 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3131 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op (M.op X1 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 (M.op (M.op X1 X0) (M.op X0 X0)) x
       have i₂ := eq1104 X0 X1 (M.op X0 X0) x
       grind)
    | exact superpose eq1104 eq1227
    | exact resolve eq1227 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq3211 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3131 X0 X1
       have i₂ := eq1587 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact superpose eq1587 eq3131
    | exact resolve eq3131 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq3242 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3211 X0 X1
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq3211
    | exact resolve eq3211 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq3343 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq164 (M.op (M.op x x) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0))) x x
       have i₂ := eq139 X0 X1 x x X4
       grind)
    | exact superpose eq139 eq164
    | exact resolve eq164 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq3369 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq164 (M.op X1 (M.op X2 X3)) X0 X3 X2
       have i₂ := eq510 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq510 eq164
    | exact resolve eq164 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq510
  have eq3516 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3369 X0 X1 X2 X3
       have i₂ := eq1064 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq1064 eq3369
    | exact resolve eq3369 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq3369
  have eq3536 : ∀ X0 X1 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq3343 X0 X1 X4 X5 X6
       have i₂ := eq1542 (M.op X4 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq1542 eq3343
    | exact resolve eq3343 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3604 : ∀ X0 X1 X5 X6 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq3536 X0 X1 x X5 X6
       have i₂ := eq181 X1 X0 x
       grind)
    | exact superpose eq181 eq3536
    | exact resolve eq3536 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3536
  have eq4334 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3242 (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) X0
       have i₂ := eq1227 X2 X0 X1
       grind)
    | exact superpose eq1227 eq3242
    | exact resolve eq3242 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq3242
  have eq4498 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4334 X0 X1 X2
       have i₂ := eq1542 (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op X1 (M.op X2 X2)) (M.op X2 X0)
       grind)
    | exact superpose eq1542 eq4334
    | exact resolve eq4334 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4513 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4498 X0 X1 X2
       have i₂ := eq3604 (M.op X1 (M.op X2 X2)) (M.op X2 X0) (M.op X2 X0) (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq3604 eq4498
    | exact resolve eq4498 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498
  have eq4519 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4513 X0 X1 X2
       have i₂ := eq3516 (M.op X2 X0) X1 X2 X2
       grind)
    | exact superpose eq3516 eq4513
    | exact resolve eq4513 eq3516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516 eq4513
  have eq4523 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4519 X0 X1 X2
       have i₂ := eq1542 (M.op X2 X0) X2 X0
       grind)
    | exact superpose eq1542 eq4519
    | exact resolve eq4519 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542 eq4519
  have eq4526 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4523 X0 X1 X2
       have i₂ := eq3604 X2 X0 X0 X2
       grind)
    | exact superpose eq3604 eq4523
    | exact resolve eq4523 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq4527 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4526 X0 X1 X2
       have i₂ := eq25 (M.op X1 (M.op X2 X2)) (M.op X2 X0)
       grind)
    | exact superpose eq25 eq4526
    | exact resolve eq4526 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4526
  have eq4528 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq4527 X0 x X2
       have i₂ := eq2141 X2 X2 X0 x
       grind)
    | exact superpose eq2141 eq4527
    | exact resolve eq4527 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141 eq4527
  have eq5444 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq88 (M.op (M.op x x) (M.op x x)) x
       have i₂ := eq24 x x x (M.op x x)
       grind)
    | exact superpose eq24 eq88
    | exact resolve eq88 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq88
  have eq5447 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5444 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq5444
    | (have j0 := eq5444 X0
       grind)
    | exact resolve eq5444 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5444
  have eq5478 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq5447 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq5447
    | (have j0 := eq5447 X0
       grind)
    | exact resolve eq5447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq5506 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5478 X0
       have j1 := eq1266 X0 X0
       grind)
    | (have r₁ := eq5478 X0
       have r₂ := eq1266 X0 X0
       grind)
    | exact resolve eq5478 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5478
  have eq5551 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5506 (σ X0)
       grind)
    | exact superpose eq5506 eq15
    | exact resolve eq15 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5562 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5551 X0
       have i₂ := eq5506 X0
       grind)
    | exact superpose eq5506 eq5551
    | exact resolve eq5551 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506 eq5551
  have eq6028 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq5562 X0
       grind)
    | exact superpose eq5562 eq9
    | exact resolve eq9 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6057 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1587 (σ X0) (σ X0)
       have i₂ := eq5562 X0
       grind)
    | exact superpose eq5562 eq1587
    | exact resolve eq1587 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq12121 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (M.op (σ (σ (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6028 (σ X0) X1
       have i₂ := eq5562 X0
       grind)
    | exact superpose eq5562 eq6028
    | exact resolve eq6028 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6028
  have eq15650 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq1918 X1 (σ X0)
       grind)
    | exact superpose eq1918 eq31
    | (have j1 := eq1918 X1 (σ X0)
       grind)
    | exact resolve eq31 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1918
  have eq15713 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15650 X0 X1
       have i₂ := eq5562 X0
       grind)
    | exact superpose eq5562 eq15650
    | (have j0 := eq15650 X0 X1
       grind)
    | exact resolve eq15650 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15779 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15713 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq15713
    | (have j0 := eq15713 X0 X1
       grind)
    | exact resolve eq15713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15713
  have eq16654 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X3)) = X0 ∨ (k (σ X3) (σ X0)) = (σ (M.op X3 X0)) ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq599 X0 (σ X0) X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq599
    | exact resolve eq599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq17052 : ∀ X0 X1 X2 X3 : G, (σ (k X3 X0)) = (σ (M.op X3 X0)) ∨ (M.op X1 (M.op (M.op X2 X1) X3)) = X0 ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16654 X0 X1 X2 X3
       have i₂ := eq15 X3 X0
       grind)
    | exact superpose eq15 eq16654
    | (have j0 := eq16654 X0 X1 X2 X3
       grind)
    | exact resolve eq16654 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16654
  have eq164974 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4528 X3 X2
       have i₂ := eq3604 X2 X3 X0 X1
       grind)
    | exact superpose eq3604 eq4528
    | exact resolve eq4528 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604 eq4528
  have eq197058 : ∀ X0 X1 : G, (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12121 (σ X0) X1
       have i₂ := eq5562 X0
       grind)
    | exact superpose eq5562 eq12121
    | exact resolve eq12121 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12121
  have eq432514 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 x x X1
       have i₂ := eq17052 X0 x x X1
       grind)
    | (have i₁ := eq1102 X0 X1 x
       have i₂ := eq17052 (M.op X0 (M.op (M.op X1 X0) x)) X1 x x
       grind)
    | exact superpose eq17052 eq1102
    | (have j1 := eq17052 X0 X1 x X1
       grind)
    | exact resolve eq1102 eq17052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq17052
  have eq433286 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq432514 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq432514 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq432514 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432514
  have eq1462430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq15779 X0 (σ X1)
       grind)
    | exact superpose eq15779 eq15
    | (have j1 := eq15779 X0 (σ X1)
       grind)
    | exact resolve eq15 eq15779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15779
  have eq1462641 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1462430 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1462430
    | (have j0 := eq1462430 X0 X1
       grind)
    | exact resolve eq1462430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462430
  have eq2722216 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1462641 x y
       grind)
    | exact superpose eq1462641 eq16
    | (have j1 := eq1462641 x y
       grind)
    | exact resolve eq16 eq1462641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462641
  have eq2724025 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq433286 y x
       grind)
    | (have r₁ := eq2722216
       have r₂ := eq433286 y x
       grind)
    | exact resolve eq2722216 eq433286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433286 eq2722216
  have eq2732239 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1266 y x
       have i₂ := eq2724025
       grind)
    | exact superpose eq2724025 eq1266
    | (have j0 := eq1266 y x
       grind)
    | exact resolve eq1266 eq2724025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq2724025
  have eq2738626 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) (M.op x x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq164974 X0 X1 x y
       have i₂ := eq2732239
       grind)
    | exact superpose eq2732239 eq164974
    | exact resolve eq164974 eq2732239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732239
  have eq2738662 : (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2738626 x x
       have i₂ := eq1123 x x x x
       grind)
    | exact superpose eq1123 eq2738626
    | exact resolve eq2738626 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq2738626
  have eq2749554 : ∀ X0 : G, y = (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq197058 X0 y
       have i₂ := eq2738662
       grind)
    | exact superpose eq2738662 eq197058
    | exact resolve eq197058 eq2738662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738662
  have eq2750450 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2749554 x
       have i₂ := eq197058 x x
       grind)
    | exact superpose eq197058 eq2749554
    | exact resolve eq2749554 eq197058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197058 eq2749554
  have eq2758536 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq164974 X0 X1 x y
       have i₂ := eq2750450
       grind)
    | exact superpose eq2750450 eq164974
    | exact resolve eq164974 eq2750450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164974
  have eq2758568 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2758536 x x
       have i₂ := eq1099 x x x
       grind)
    | exact superpose eq1099 eq2758536
    | exact resolve eq2758536 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq2758536
  have eq2765309 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6057 y
       have i₂ := eq2758568
       grind)
    | exact superpose eq2758568 eq6057
    | exact resolve eq6057 eq2758568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057 eq2758568
  have eq2904508 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2765309
       grind)
    | exact superpose eq2765309 eq16
    | exact resolve eq16 eq2765309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765309
  have eq2906874 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq2904508
       have i₂ := eq2750450
       grind)
    | exact superpose eq2750450 eq2904508
    | exact resolve eq2904508 eq2750450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750450 eq2904508
  have eq2906881 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq2906874
  have eq2906882 : x = y := by grind
  clear eq2906881
  have eq2910062 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2906882
       grind)
    | exact superpose eq2906882 eq16
    | exact resolve eq16 eq2906882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906882
  have eq2910068 : False := by grind
  exact eq2910068
