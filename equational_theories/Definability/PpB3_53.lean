import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq280 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq772 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq280
    | (have j0 := eq280 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq280 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq13795 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq13800 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq772
  have eq13825 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13800
  have eq13828 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq13795
  have eq13850 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13825 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq13825
    | (have j0 := eq13825 X0
       grind)
    | exact resolve eq13825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13825
  have eq13874 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq13850
  have eq13900 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq13828
       grind)
    | exact superpose eq13828 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13828
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13828
       grind)
    | exact resolve eq13 eq13828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13901 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ x) X0 (σ y)
       have i₂ := eq13828
       grind)
    | exact superpose eq13828 eq64
    | exact resolve eq64 eq13828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13902 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq13900
  have eq13903 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq13902
  have eq13905 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13903
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq13903
    | exact resolve eq13903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13903
  have eq13911 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq13905
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq13905 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13905
  have eq25160 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13901 X0 (σ x)
       have i₂ := eq13828
       grind)
    | exact superpose eq13828 eq13901
    | exact resolve eq13901 eq13828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13828 eq13901
  have eq25216 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq25160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25160
  have eq25308 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25216 (σ x)
       grind)
    | exact superpose eq25216 eq16
    | exact resolve eq16 eq25216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25216
  have eq25325 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25308
       have r₂ := eq13911
       grind)
    | exact resolve eq25308 eq13911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13911 eq25308
  have eq25511 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq25325
  have eq25542 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25511
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq25511
    | exact resolve eq25511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25511
  have eq25578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq25542
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq25542 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25542
  have eq25602 : y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25578
       have r₂ := eq16
       grind)
    | exact resolve eq25578 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25578
  have eq25607 : y ≠ y ∨ x = (M.op y y) ∨ (M.op x x) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25602
       grind)
    | exact superpose eq25602 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25602
       grind)
    | exact resolve eq13 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25608 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 x X0 y
       have i₂ := eq25602
       grind)
    | exact superpose eq25602 eq64
    | exact resolve eq64 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25609 : y ≠ y ∨ x = (M.op y y) ∨ (M.op x x) = (k x y) := by grind
  clear eq25607
  have eq25610 : (M.op x x) = (k x y) ∨ x = (M.op y y) := by grind
  clear eq25609
  have eq25613 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq280 x y
       have i₂ := eq25610
       grind)
    | exact superpose eq25610 eq280
    | (have j0 := eq280 x y
       grind)
    | exact resolve eq280 eq25610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq25617 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq25608 X0 x
       have i₂ := eq25602
       grind)
    | exact superpose eq25602 eq25608
    | exact resolve eq25608 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25608
  have eq25673 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq25617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25617
  have eq25698 : (σ (M.op (M.op y x) y)) = (M.op (σ (M.op y x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq773 y
       have i₂ := eq25673 y
       grind)
    | exact superpose eq25673 eq773
    | exact resolve eq773 eq25673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25746 : (M.op (σ (M.op y x)) (σ y)) = (σ (M.op (M.op y x) x)) ∨ (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25673 eq25698
    | exact resolve eq25698 eq25673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25698
  have eq25757 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25602 eq25746
    | exact resolve eq25746 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25746
  have eq25758 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) := by grind
  clear eq25757
  have eq25760 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25602 eq25758
    | exact resolve eq25758 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25758
  have eq25762 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25602 eq25760
    | exact resolve eq25760 eq25602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25602 eq25760
  have eq25763 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq25762
  have eq333823 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25613
       grind)
    | exact superpose eq25613 eq16
    | exact resolve eq16 eq25613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25613
  have eq333855 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25673 eq333823
    | exact resolve eq333823 eq25673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333823
  have eq333856 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq333855
  have eq333874 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq333856
       grind)
    | exact superpose eq333856 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq333856
       grind)
    | exact resolve eq13 eq333856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333875 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ x) X0 (σ y)
       have i₂ := eq333856
       grind)
    | exact superpose eq333856 eq64
    | exact resolve eq64 eq333856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq333856
  have eq333876 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq333874
  have eq333877 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq333876
  have eq333881 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq333877
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq333877
    | exact resolve eq333877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333877
  have eq333892 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25610 eq333881
    | exact resolve eq333881 eq25610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25610 eq333881
  have eq334080 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq333875 X0 (σ y)
       have i₂ := eq25763
       grind)
    | exact superpose eq25763 eq333875
    | exact resolve eq333875 eq25763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333875
  have eq334212 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq334080 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334080
  have eq334368 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq334212 (σ x)
       grind)
    | exact superpose eq334212 eq16
    | exact resolve eq16 eq334212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334212
  have eq334431 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq25673 eq334368
    | exact resolve eq334368 eq25673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25673 eq334368
  have eq334590 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq334431
       have i₂ := eq333892
       grind)
    | exact superpose eq333892 eq334431
    | (have r₁ := eq334431
       have r₂ := eq333892
       grind)
    | exact resolve eq334431 eq333892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333892 eq334431
  have eq334596 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq334590
  have eq334597 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq334596
  have eq334603 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25763
       have i₂ := eq334597
       grind)
    | exact superpose eq334597 eq25763
    | exact resolve eq25763 eq334597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334597
  have eq334705 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq334603
  have eq334870 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq334705 eq25763
    | exact resolve eq25763 eq334705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25763
  have eq334907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13874 y
       have i₂ := eq334705
       grind)
    | exact superpose eq334705 eq13874
    | (have j0 := eq13874 y
       grind)
    | exact resolve eq13874 eq334705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334916 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq334907
       have r₂ := eq16
       grind)
    | exact resolve eq334907 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334907
  have eq336315 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq334870
       grind)
    | exact superpose eq334870 eq66
    | exact resolve eq66 eq334870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336358 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq336315
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq336315
    | exact resolve eq336315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336315
  have eq336374 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq334870 eq336358
    | exact resolve eq336358 eq334870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334870 eq336358
  have eq336388 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq336374
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq336374
    | exact resolve eq336374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336374
  have eq336429 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq336388
       grind)
    | exact superpose eq336388 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq336388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336388
  have eq336430 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq336429
  have eq336466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13874 y
       have i₂ := eq336430
       grind)
    | exact superpose eq336430 eq13874
    | (have j0 := eq13874 y
       grind)
    | exact resolve eq13874 eq336430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13874
  have eq336475 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq336466
       have r₂ := eq16
       grind)
    | exact resolve eq336466 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336466
  have eq337119 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq336475
       grind)
    | exact superpose eq336475 eq66
    | exact resolve eq66 eq336475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337162 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq337119
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq337119
    | exact resolve eq337119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337119
  have eq337177 : (τ (σ y)) = (k y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq336475 eq337162
    | exact resolve eq337162 eq336475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336475 eq337162
  have eq337191 : y = (k y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq337177
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq337177
    | exact resolve eq337177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337177
  have eq337236 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq337191
       grind)
    | exact superpose eq337191 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq337191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337191
  have eq337237 : y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq337236
  have eq337255 : x = y ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq336430 eq337237
    | exact resolve eq337237 eq336430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337237
  have eq337256 : x = (M.op x x) ∨ x = y := by grind
  clear eq337255
  have eq337272 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq337256 eq336430
    | exact resolve eq336430 eq337256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336430 eq337256
  have eq337291 : x = (M.op x x) := by grind
  clear eq337272
  have eq337309 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq773 x
       have i₂ := eq337291
       grind)
    | exact superpose eq337291 eq773
    | (have j0 := eq773 x
       grind)
    | exact resolve eq773 eq337291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq337318 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq337309
  have eq337324 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq337318
       have i₂ := eq337291
       grind)
    | exact superpose eq337291 eq337318
    | exact resolve eq337318 eq337291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337318
  have eq337325 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq337324
  have eq339069 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq334916
       grind)
    | exact superpose eq334916 eq66
    | exact resolve eq66 eq334916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq339112 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq339069
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq339069
    | exact resolve eq339069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339069
  have eq339127 : (τ (σ y)) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq334916 eq339112
    | exact resolve eq339112 eq334916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334916 eq339112
  have eq339141 : y = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq339127
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq339127
    | exact resolve eq339127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339127
  have eq339186 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq339141
       grind)
    | exact superpose eq339141 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq339141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339141
  have eq339187 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq339186
  have eq339205 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq334705 eq339187
    | exact resolve eq339187 eq334705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334705 eq339187
  have eq339206 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq339205
  have eq339224 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq339206
       grind)
    | exact superpose eq339206 eq10
    | exact resolve eq10 eq339206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339206
  have eq339465 : x = y ∨ x = y := by
    first
    | (have i₁ := eq339224
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq339224
    | exact resolve eq339224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339224
  have eq339466 : x = y := by grind
  clear eq339465
  have eq339537 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq339466
       grind)
    | exact superpose eq339466 eq16
    | exact resolve eq16 eq339466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339466
  have eq339570 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq339537
       have i₂ := eq337291
       grind)
    | exact superpose eq337291 eq339537
    | exact resolve eq339537 eq337291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337291 eq339537
  have eq339571 : False := by grind
  exact eq339571

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq280 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq279
    | (have j0 := eq279 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq279 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq279
  have eq9525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq771 x y
       grind)
    | exact superpose eq771 eq16
    | (have j1 := eq771 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq771 x y
       grind)
    | exact resolve eq16 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq9568 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9525
  have eq9958 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9568
  have eq9970 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9958
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9958
    | exact resolve eq9958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9958
  have eq9984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq9970
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq9970 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq9990 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9984
       have r₂ := eq16
       grind)
    | exact resolve eq9984 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9984
  have eq10255 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9990
       grind)
    | exact superpose eq9990 eq16
    | exact resolve eq16 eq9990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10259 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ y) X0 (σ x)
       have i₂ := eq9990
       grind)
    | exact superpose eq9990 eq64
    | exact resolve eq64 eq9990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10269 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10259 X0 (σ y)
       have i₂ := eq9990
       grind)
    | exact superpose eq9990 eq10259
    | exact resolve eq10259 eq9990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10259
  have eq10291 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10269
  have eq10321 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9990
       have i₂ := eq10291 (σ x)
       grind)
    | exact superpose eq10291 eq9990
    | exact resolve eq9990 eq10291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10291
  have eq10338 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10321
  have eq10353 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq10338
       grind)
    | exact superpose eq10338 eq66
    | exact resolve eq66 eq10338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10365 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10353
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10353
    | exact resolve eq10353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10353
  have eq10369 : (k x x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10338 eq10365
    | exact resolve eq10365 eq10338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10338 eq10365
  have eq10370 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10369
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10369
    | exact resolve eq10369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10369
  have eq10373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq772 x
       have i₂ := eq10370
       grind)
    | exact superpose eq10370 eq772
    | exact resolve eq772 eq10370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10376 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq10370
  have eq10381 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq10373
       have r₂ := eq16
       grind)
    | exact resolve eq10373 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10373
  have eq10702 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq280 X0 X1
       grind)
    | exact superpose eq280 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq280 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq280 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq280 X0 X0
       grind)
    | exact resolve eq13 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10704 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq10707 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702
  have eq10721 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10707 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq10707 X0 X0
       have r₂ := eq13 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq10707 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq10707 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10707
  have eq10738 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10721 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq10721
    | (have j0 := eq10721 X0 X1
       grind)
    | exact resolve eq10721 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq10721
  have eq10764 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10704 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10704
    | (have j0 := eq10704 (σ X1) (σ X0)
       grind)
    | exact resolve eq10704 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10704
  have eq10842 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10764 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10764
    | (have j0 := eq10764 X0 X1
       grind)
    | exact resolve eq10764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10764
  have eq10876 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10842 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq10842
    | (have j0 := eq10842 X0 X1
       grind)
    | exact resolve eq10842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10842
  have eq10908 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10876 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10876
    | (have j0 := eq10876 X0 X1
       grind)
    | exact resolve eq10876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10876
  have eq10938 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10908 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10908
    | (have j0 := eq10908 X0 X1
       grind)
    | exact resolve eq10908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908
  have eq10963 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10938 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10938
    | (have j0 := eq10938 X0 X1
       grind)
    | exact resolve eq10938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10938
  have eq10984 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10963 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10963
    | (have j0 := eq10963 X0 X1
       grind)
    | exact resolve eq10963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10963
  have eq11020 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10984 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10984
    | (have j0 := eq10984 (σ X0) (σ X1)
       grind)
    | exact resolve eq10984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10984
  have eq11267 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10738 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10738
    | (have j0 := eq10738 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq10738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10738
  have eq11344 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11267 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11267
    | (have j0 := eq11267 X0 X1
       grind)
    | exact resolve eq11267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11267
  have eq11376 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11344 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11344
    | (have j0 := eq11344 X0 X1
       grind)
    | exact resolve eq11344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11344
  have eq11403 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11376 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11376
    | (have j0 := eq11376 X0 X1
       grind)
    | exact resolve eq11376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376
  have eq11428 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11403 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11403
    | (have j0 := eq11403 X0 X1
       grind)
    | exact resolve eq11403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11403
  have eq11449 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11428 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11428
    | (have j0 := eq11428 X0 X1
       grind)
    | exact resolve eq11428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11428
  have eq11470 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11449 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11449
    | (have j0 := eq11449 X0 X1
       grind)
    | exact resolve eq11449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11449
  have eq11822 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq10381
  have eq11845 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11822
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11822
    | exact resolve eq11822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11822
  have eq11863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq10376 eq11845
    | exact resolve eq11845 eq10376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376 eq11845
  have eq11869 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq11863
       have r₂ := eq16
       grind)
    | exact resolve eq11863 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11863
  have eq11878 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ y) X0 (σ x)
       have i₂ := eq11869
       grind)
    | exact superpose eq11869 eq64
    | exact resolve eq64 eq11869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11895 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq11878 X0 (σ y)
       have i₂ := eq11869
       grind)
    | exact superpose eq11869 eq11878
    | exact resolve eq11878 eq11869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11878
  have eq11939 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq11895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11895
  have eq11980 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11869
       have i₂ := eq11939 (σ x)
       grind)
    | exact superpose eq11939 eq11869
    | exact resolve eq11869 eq11939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11869 eq11939
  have eq12010 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq11980
  have eq12027 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq12010
       grind)
    | exact superpose eq12010 eq66
    | exact resolve eq66 eq12010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq12039 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12027
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12027
    | exact resolve eq12027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12027
  have eq12043 : (k x x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq12010 eq12039
    | exact resolve eq12039 eq12010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12010 eq12039
  have eq12044 : x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12043
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12043
    | exact resolve eq12043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12043
  have eq12045 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq12044
  have eq12067 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11470 x x
       have i₂ := eq12045
       grind)
    | exact superpose eq12045 eq11470
    | (have j0 := eq11470 x x
       grind)
    | (have r₁ := eq11470 x x
       have r₂ := eq12045
       grind)
    | exact resolve eq11470 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11470 eq12045
  have eq12071 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12067
  have eq12072 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq12071
  have eq12097 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12072 eq9990
    | exact resolve eq9990 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9990
  have eq12098 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12072 eq10255
    | exact resolve eq10255 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10255
  have eq12109 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 y X0 x
       have i₂ := eq12072
       grind)
    | exact superpose eq12072 eq64
    | exact resolve eq64 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12172 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12109 X0 y
       have i₂ := eq12072
       grind)
    | exact superpose eq12072 eq12109
    | exact resolve eq12109 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12109
  have eq12192 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq12172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12172
  have eq12203 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12192 x
       have i₂ := eq12072
       grind)
    | exact superpose eq12072 eq12192
    | exact resolve eq12192 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12072 eq12192
  have eq12225 : x = (M.op x x) := by grind
  clear eq12203
  have eq12241 : x = (M.op x x) := by grind
  clear eq12225
  have eq12244 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq772 x
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq772
    | (have j0 := eq772 x
       grind)
    | exact resolve eq772 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq12247 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 x X0 x
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq64
    | exact resolve eq64 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12249 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12244
  have eq12250 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12249
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq12249
    | exact resolve eq12249 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12249
  have eq12251 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12250
  have eq13152 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq12097
       grind)
    | exact superpose eq12097 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12097
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12097
       grind)
    | exact resolve eq13 eq12097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097
  have eq13154 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13152
  have eq13158 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13154
       have i₂ := eq12251
       grind)
    | exact superpose eq12251 eq13154
    | exact resolve eq13154 eq12251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13154
  have eq13160 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13158
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq13158
    | exact resolve eq13158 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13158
  have eq13162 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13160
       have i₂ := eq12251
       grind)
    | exact superpose eq12251 eq13160
    | exact resolve eq13160 eq12251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13160
  have eq13486 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13162
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq13162
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq13162 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13162
  have eq13579 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq13486
  have eq13654 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13579
       have r₂ := eq12098
       grind)
    | exact resolve eq13579 eq12098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12098 eq13579
  have eq13656 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13654
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq13654
    | exact resolve eq13654 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13654
  have eq13657 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13656
  have eq13665 : x ≠ x ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq13657
       grind)
    | exact superpose eq13657 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13657
       grind)
    | exact resolve eq13 eq13657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13666 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 y X0 x
       have i₂ := eq13657
       grind)
    | exact superpose eq13657 eq64
    | exact resolve eq64 eq13657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq13657
  have eq13667 : y = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13665
  have eq13669 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13666 X0 x
       have i₂ := eq12247 X0 x
       grind)
    | exact superpose eq12247 eq13666
    | exact resolve eq13666 eq12247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12247 eq13666
  have eq13670 : x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13667
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq13667
    | exact resolve eq13667 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13667
  have eq13671 : x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq13670
  have eq13674 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13671
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq13671
    | exact resolve eq13671 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13671
  have eq13684 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11020 y x
       have i₂ := eq13674
       grind)
    | exact superpose eq13674 eq11020
    | (have j0 := eq11020 y x
       grind)
    | exact resolve eq11020 eq13674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11020 eq13674
  have eq13689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13684
  have eq13696 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13689
       have i₂ := eq12251
       grind)
    | exact superpose eq12251 eq13689
    | exact resolve eq13689 eq12251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13689
  have eq13697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13696
  have eq13751 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq13697
       grind)
    | exact superpose eq13697 eq16
    | exact resolve eq16 eq13697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13697
  have eq13764 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13669 eq13751
    | exact resolve eq13751 eq13669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13669 eq13751
  have eq13768 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13764
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq13764
    | exact resolve eq13764 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13764
  have eq13769 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq13768
  have eq13773 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13769
       grind)
    | exact superpose eq13769 eq10
    | exact resolve eq10 eq13769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13769
  have eq13930 : x = y ∨ x = y := by
    first
    | (have i₁ := eq13773
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13773
    | exact resolve eq13773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq13931 : x = y := by grind
  clear eq13930
  have eq13938 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13931
       grind)
    | exact superpose eq13931 eq16
    | exact resolve eq16 eq13931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13931
  have eq13939 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13938
       have i₂ := eq12241
       grind)
    | exact superpose eq12241 eq13938
    | exact resolve eq13938 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12241 eq13938
  have eq13940 : False := by grind
  exact eq13940

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq285 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq272 (τ X0)
       grind)
    | exact superpose eq272 eq17
    | exact resolve eq17 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq297 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq292
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq304 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq285
    | exact resolve eq285 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq317 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq297 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq297
    | exact resolve eq297 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq297
  have eq354 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq10
    | exact resolve eq10 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq415
    | (have j0 := eq415 (σ X0) (σ X1)
       grind)
    | exact resolve eq415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq416 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq416 X0 X1
       grind)
    | exact superpose eq416 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq416 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq416 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq416 X0 X1
       grind)
    | exact resolve eq13 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (M.op (σ X0) (σ X1)) X3)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 (σ X0) X2 (σ X1)
       have i₂ := eq416 X0 X1
       grind)
    | (have i₁ := eq63 X0 (σ X1) X2 (σ X0)
       have i₂ := eq416 X0 X1
       grind)
    | exact superpose eq416 eq63
    | (have j1 := eq416 X0 X1
       grind)
    | exact resolve eq63 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq465 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq472 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X0 X1 X2 x
       have i₂ := eq63 x (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq63 eq467
    | (have j0 := eq467 X0 X1 X2 x
       grind)
    | exact resolve eq467 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq474 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq304 X1
       grind)
    | exact superpose eq304 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq485 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq304 X1
       grind)
    | exact superpose eq304 eq474
    | (have j0 := eq474 X0 X1
       grind)
    | exact resolve eq474 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq489 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq485
    | (have j0 := eq485 X0 X1
       grind)
    | exact resolve eq485 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq6113 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq489 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq489
    | (have j0 := eq489 X0 (τ X1)
       grind)
    | exact resolve eq489 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq489
  have eq6223 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6113 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6113
    | (have j0 := eq6113 X0 X1
       grind)
    | exact resolve eq6113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq6248 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6223 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6223
    | (have j0 := eq6223 X0 X1
       grind)
    | exact resolve eq6223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6223
  have eq6266 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6248 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6248
    | (have j0 := eq6248 X0 X1
       grind)
    | exact resolve eq6248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6248
  have eq6278 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X1 X1))) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6266 X0 X1
       have i₂ := eq354 X1
       grind)
    | exact superpose eq354 eq6266
    | (have j0 := eq6266 X0 X1
       grind)
    | exact resolve eq6266 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6266
  have eq6290 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6278 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6278
    | (have j0 := eq6278 X0 X1
       grind)
    | exact resolve eq6278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278
  have eq6300 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6290 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6290
    | (have j0 := eq6290 X0 X1
       grind)
    | exact resolve eq6290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6290
  have eq6308 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq6300 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq6300 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq6300 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6314 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (τ (M.op X1 X1))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6308 X0 X1
       have i₂ := eq354 X1
       grind)
    | exact superpose eq354 eq6308
    | (have j0 := eq6308 X0 X1
       grind)
    | exact resolve eq6308 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq6308
  have eq6317 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6314 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6314
    | (have j0 := eq6314 X0 X1
       grind)
    | exact resolve eq6314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314
  have eq6320 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6317 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6317
    | (have j0 := eq6317 X0 X1
       grind)
    | exact resolve eq6317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6317
  have eq6436 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq6320 X1 (σ X0)
       grind)
    | exact superpose eq6320 eq22
    | (have j1 := eq6320 X1 (σ X0)
       grind)
    | exact resolve eq22 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6569 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6436 X0 X1
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq6436
    | (have j0 := eq6436 X0 X1
       grind)
    | exact resolve eq6436 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6436
  have eq6659 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6569 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6569
    | (have j0 := eq6569 X0 X1
       grind)
    | exact resolve eq6569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6569
  have eq7320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6659 X1 (σ X0)
       grind)
    | exact superpose eq6659 eq15
    | (have j1 := eq6659 X1 (σ X0)
       grind)
    | exact resolve eq15 eq6659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6659
  have eq7387 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7320 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7320
    | (have j0 := eq7320 X0 X1
       grind)
    | exact resolve eq7320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7320
  have eq7438 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | exact superpose eq6320 eq7387
    | (have j0 := eq7387 X0 X1
       have j1 := eq6320 X0 X1
       grind)
    | exact resolve eq7387 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320 eq7387
  have eq7884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7438 x y
       grind)
    | exact superpose eq7438 eq16
    | (have j1 := eq7438 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq7438 x y
       grind)
    | exact resolve eq16 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7438
  have eq7937 : (k x y) = (M.op y y) := by grind
  clear eq7884
  have eq7986 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7937
       have i₂ := eq415 x y
       grind)
    | exact superpose eq415 eq7937
    | (have j1 := eq415 x y
       grind)
    | exact resolve eq7937 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7988 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq472 x y X0
       have i₂ := eq7937
       grind)
    | exact superpose eq7937 eq472
    | (have j0 := eq472 y x X0
       grind)
    | exact resolve eq472 eq7937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11709 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq7988 X0
       grind)
    | exact superpose eq7988 eq16
    | (have j1 := eq7988 X0
       grind)
    | exact resolve eq16 eq7988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7988
  have eq11772 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq11709 X0
       have i₂ := eq7986
       grind)
    | exact superpose eq7986 eq11709
    | (have j0 := eq11709 X0
       grind)
    | exact resolve eq11709 eq7986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709
  have eq11778 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq11772 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11772
  have eq11838 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11778 (σ x)
       grind)
    | exact superpose eq11778 eq16
    | exact resolve eq16 eq11778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11839 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq304 y
       have i₂ := eq11778 (σ y)
       grind)
    | exact superpose eq11778 eq304
    | exact resolve eq304 eq11778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11874 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq7986 eq11839
    | exact resolve eq11839 eq7986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11839
  have eq11875 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq11838
       have i₂ := eq304 x
       grind)
    | exact superpose eq304 eq11838
    | exact resolve eq11838 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11838
  have eq11944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq416 x y
       have i₂ := eq11874
       grind)
    | exact superpose eq11874 eq416
    | (have j0 := eq416 x y
       grind)
    | exact resolve eq416 eq11874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq11874
  have eq11983 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq11944
       have r₂ := eq16
       grind)
    | exact resolve eq11944 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11944
  have eq12004 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq11983
       have i₂ := eq7937
       grind)
    | exact superpose eq7937 eq11983
    | exact resolve eq11983 eq7937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11983
  have eq12017 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq11778 eq12004
    | exact resolve eq12004 eq11778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11778 eq12004
  have eq12025 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq12017
       have i₂ := eq304 x
       grind)
    | exact superpose eq304 eq12017
    | exact resolve eq12017 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12017
  have eq12030 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq7986 eq12025
    | exact resolve eq12025 eq7986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7986 eq12025
  have eq12033 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq12030
       have r₂ := eq11875
       grind)
    | exact resolve eq12030 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875 eq12030
  have eq12041 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 y
       have i₂ := eq12033
       grind)
    | exact superpose eq12033 eq63
    | exact resolve eq63 eq12033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12033
  have eq12054 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12041 X0 x
       have i₂ := eq63 x y X0 x
       grind)
    | exact superpose eq63 eq12041
    | exact resolve eq12041 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq12041
  have eq12055 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12054 x
       grind)
    | exact superpose eq12054 eq16
    | exact resolve eq16 eq12054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12063 : (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq7937
       have i₂ := eq12054 y
       grind)
    | exact superpose eq12054 eq7937
    | exact resolve eq7937 eq12054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7937
  have eq12167 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq415 x y
       have i₂ := eq12063
       grind)
    | exact superpose eq12063 eq415
    | (have j0 := eq415 x y
       grind)
    | exact resolve eq415 eq12063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq12176 : (M.op x y) = (M.op y x) := by grind
  clear eq12167
  have eq12183 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq12176
       have i₂ := eq12054 x
       grind)
    | exact superpose eq12054 eq12176
    | exact resolve eq12176 eq12054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12054 eq12176
  have eq12188 : (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq12063
       have i₂ := eq12183
       grind)
    | exact superpose eq12183 eq12063
    | exact resolve eq12063 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12063 eq12183
  have eq12221 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq472 x y X0
       have i₂ := eq12188
       grind)
    | exact superpose eq12188 eq472
    | (have j0 := eq472 y x X0
       grind)
    | exact resolve eq472 eq12188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq12188
  have eq12230 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq12221 X0
       grind)
    | (have r₁ := eq12221 X0
       have r₂ := eq12055
       grind)
    | exact resolve eq12221 eq12055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12221
  have eq12417 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12055
       have i₂ := eq12230 (σ x)
       grind)
    | exact superpose eq12230 eq12055
    | exact resolve eq12055 eq12230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12055 eq12230
  have eq12418 : False := by grind
  exact eq12418

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq22
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq270 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq271 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 (σ X0) (σ X1)
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq270
    | (have j0 := eq270 (τ X0) (τ X1)
       grind)
    | exact resolve eq270 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq405 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq271 X0 X1
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq271
    | (have j0 := eq271 X0 X1
       have j1 := eq270 (σ X0) (σ X1)
       grind)
    | exact resolve eq271 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq271
  have eq541 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq272 X0 X0
       grind)
    | exact superpose eq272 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq272 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq272 X0 X0
       grind)
    | exact resolve eq12 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq548 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq541 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq541 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq599 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq548 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq548
    | (have j0 := eq548 (σ X0) X1
       grind)
    | exact resolve eq548 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq600 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq603 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq600
    | (have j0 := eq600 X0 X1
       grind)
    | exact resolve eq600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq608 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq603 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq603
    | (have j0 := eq603 (σ X0) X1
       grind)
    | exact resolve eq603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq2638 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq405 x y
       grind)
    | exact superpose eq405 eq16
    | (have j1 := eq405 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq405 x y
       grind)
    | exact resolve eq16 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq2650 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2638
  have eq2665 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq2650
       grind)
    | exact superpose eq2650 eq63
    | exact resolve eq63 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2674 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2665 X0 (σ x)
       have i₂ := eq2650
       grind)
    | exact superpose eq2650 eq2665
    | exact resolve eq2665 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2686 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq2692 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq2686 (σ y)
       grind)
    | exact superpose eq2686 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | exact resolve eq12 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2697 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2686 (σ x)
       grind)
    | exact superpose eq2686 eq16
    | exact resolve eq16 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2707 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2692 X0
       grind)
    | (have r₁ := eq2692 X0
       have r₂ := eq2650
       grind)
    | exact resolve eq2692 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2708 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2686 eq2707
    | exact resolve eq2707 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq2707
  have eq2710 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2708 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq2708
    | exact resolve eq2708 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2730 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq548 (σ y) X0
       have i₂ := eq2708 (σ y)
       grind)
    | exact superpose eq2708 eq548
    | (have j0 := eq548 (σ y) X0
       grind)
    | exact resolve eq548 eq2708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq2708
  have eq2794 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ x))) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2730 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2730
    | (have j0 := eq2730 X0
       grind)
    | exact resolve eq2730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2799 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y ≠ (τ (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2794 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2794
    | exact resolve eq2794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2802 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y ≠ (τ (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2650 eq2799
    | (have j0 := eq2799 X0
       grind)
    | exact resolve eq2799 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq2799
  have eq2804 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2802 X0
       grind)
    | (have r₁ := eq2802 X0
       have r₂ := eq10 y
       grind)
    | exact resolve eq2802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq2969 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2804 eq2710
    | exact resolve eq2710 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710 eq2804
  have eq3061 : y = (M.op y x) := by
    first
    | (have r₁ := eq2697
       have r₂ := eq2969 x
       grind)
    | exact resolve eq2697 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697 eq2969
  have eq3103 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 y
       have i₂ := eq3061
       grind)
    | exact superpose eq3061 eq63
    | exact resolve eq63 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq3106 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3103 X0 x
       have i₂ := eq3061
       grind)
    | exact superpose eq3061 eq3103
    | exact resolve eq3103 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3119 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3106 x
       grind)
    | exact superpose eq3106 eq16
    | exact resolve eq16 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3120 : ∀ X0 : G, y ≠ (M.op y x) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq3106 y
       grind)
    | exact superpose eq3106 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3130 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq3120 X0
       grind)
    | (have r₁ := eq3120 X0
       have r₂ := eq3061
       grind)
    | exact resolve eq3120 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3131 : ∀ X0 : G, (k X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3130 X0
       have i₂ := eq3106 X0
       grind)
    | exact superpose eq3106 eq3130
    | exact resolve eq3130 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106 eq3130
  have eq3133 : ∀ X0 : G, (σ y) ≠ (σ (M.op y x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq608 y X0
       have i₂ := eq3131 y
       grind)
    | exact superpose eq3131 eq608
    | (have j0 := eq608 y X0
       grind)
    | exact resolve eq608 eq3131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq3173 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3133 X0
       have i₂ := eq3061
       grind)
    | exact superpose eq3061 eq3133
    | (have j0 := eq3133 X0
       grind)
    | exact resolve eq3133 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061 eq3133
  have eq3174 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3297 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq3174 (σ X0)
       grind)
    | exact superpose eq3174 eq15
    | exact resolve eq15 eq3174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq3363 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq3297 X0
       have i₂ := eq3131 X0
       grind)
    | exact superpose eq3131 eq3297
    | exact resolve eq3297 eq3131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131 eq3297
  have eq3643 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3119
       have i₂ := eq3363 x
       grind)
    | exact superpose eq3363 eq3119
    | (have r₁ := eq3119
       have r₂ := eq3363 x
       grind)
    | exact resolve eq3119 eq3363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119 eq3363
  have eq3666 : False := by grind
  exact eq3666

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X2 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq105
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq530 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 X0
       have i₂ := eq14 (τ X0) (τ X1)
       grind)
    | exact superpose eq14 eq45
    | (have j1 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq530
    | (have j0 := eq530 X0 X1
       grind)
    | exact resolve eq530 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq530
  have eq546 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq4193 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq546
    | (have j0 := eq546 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq546 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4194 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq546
    | (have j0 := eq546 (σ X0) (σ X1)
       grind)
    | exact resolve eq546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4298 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4194 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq4194
    | (have j0 := eq4194 X0 X1
       grind)
    | exact resolve eq4194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4194
  have eq39203 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have j0 := eq539 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq40715 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) ≠ (τ (σ (k X0 X1))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39203 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39203
    | (have j0 := eq39203 (σ X0) (σ X1)
       grind)
    | exact resolve eq39203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39203
  have eq40867 : ∀ X0 X1 : G, (k X0 X1) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40715 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq40715
    | (have j0 := eq40715 X0 X1
       grind)
    | exact resolve eq40715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40715
  have eq40920 : ∀ X0 X1 : G, (k X0 X1) ≠ (τ (σ (M.op X0 X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40867 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq40867
    | (have j0 := eq40867 X0 X1
       grind)
    | exact resolve eq40867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40867
  have eq40963 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40920 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq40920
    | (have j0 := eq40920 X0 X1
       grind)
    | exact resolve eq40920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40920
  have eq40988 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40963 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq40963
    | (have j0 := eq40963 X0 X1
       grind)
    | exact resolve eq40963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40963
  have eq41009 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40988 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40988
    | (have j0 := eq40988 X0 X1
       grind)
    | exact resolve eq40988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40988
  have eq41029 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41009 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq41009
    | (have j0 := eq41009 X0 X1
       grind)
    | exact resolve eq41009 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41009
  have eq41043 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41029 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq41029
    | (have j0 := eq41029 X0 X1
       grind)
    | exact resolve eq41029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41029
  have eq41056 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41043 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq41043
    | (have j0 := eq41043 X0 X1
       grind)
    | exact resolve eq41043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41043
  have eq41065 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41056 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41056
    | (have j0 := eq41056 X0 X1
       grind)
    | exact resolve eq41056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41056
  have eq41086 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41065 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq41065
    | (have j0 := eq41065 (σ X0) (σ X1)
       grind)
    | exact resolve eq41065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41065
  have eq41185 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41086 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq41086
    | (have j0 := eq41086 X0 X1
       grind)
    | exact resolve eq41086 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41086
  have eq41197 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41185 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq41185
    | (have j0 := eq41185 X0 X1
       grind)
    | exact resolve eq41185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41185
  have eq52447 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 (σ X0) (σ (σ X1))
       have i₂ := eq4298 X0 X1
       grind)
    | exact superpose eq4298 eq167
    | (have j0 := eq167 (σ X0) (σ (σ X1))
       have j1 := eq4298 X0 X1
       grind)
    | exact resolve eq167 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq52489 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq52447 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52447
  have eq52519 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52489 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq52489
    | (have j0 := eq52489 X0 X1
       grind)
    | exact resolve eq52489 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52489
  have eq52520 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq52519 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52519
  have eq52598 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52520 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq52520
    | (have j0 := eq52520 X0 X1
       grind)
    | exact resolve eq52520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52520
  have eq52640 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52598 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52598
    | (have j0 := eq52598 X0 X1
       grind)
    | exact resolve eq52598 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52598
  have eq57594 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq4193 x y
       grind)
    | exact superpose eq4193 eq16
    | (have j1 := eq4193 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4193 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4193 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq4193 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq57671 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq57594
  have eq57878 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq167 x (σ y)
       have i₂ := eq57671
       grind)
    | exact superpose eq57671 eq167
    | (have j0 := eq167 x (σ y)
       grind)
    | (have r₁ := eq167 x (σ y)
       have r₂ := eq57671
       grind)
    | exact resolve eq167 eq57671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57882 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (σ y) X0 (σ x)
       have i₂ := eq57671
       grind)
    | exact superpose eq57671 eq105
    | exact resolve eq105 eq57671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57908 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq57878
  have eq57909 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq57908
  have eq57920 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq57882 X0 x
       have i₂ := eq106 x X0 x
       grind)
    | exact superpose eq106 eq57882
    | exact resolve eq57882 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57882
  have eq57922 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq57909
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq57909
    | exact resolve eq57909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57909
  have eq57928 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq14 eq57922
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq57922 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57922
  have eq57931 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq57928
       grind)
    | exact superpose eq57928 eq10
    | exact resolve eq10 eq57928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57928
  have eq58081 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq57931
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq57931
    | exact resolve eq57931 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57931
  have eq58083 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 y X0 x
       have i₂ := eq58081
       grind)
    | exact superpose eq58081 eq105
    | exact resolve eq105 eq58081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58081
  have eq58111 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq58083 X0 x
       have i₂ := eq105 x x X0 x
       grind)
    | exact superpose eq105 eq58083
    | exact resolve eq58083 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58083
  have eq58125 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ y = X0 ∨ (k y X0) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq58111 y
       grind)
    | exact superpose eq58111 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq58111 x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq58111 y
       grind)
    | exact resolve eq13 eq58111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58197 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ y = X0 ∨ y = (k X0 y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq58111 X0
       grind)
    | exact superpose eq58111 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq58111 x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq58111 y
       grind)
    | exact resolve eq13 eq58111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58412 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq57920 (σ y)
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq57920
    | exact resolve eq57920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57920
  have eq58787 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq167 y (σ x)
       have i₂ := eq58412
       grind)
    | exact superpose eq58412 eq167
    | (have j0 := eq167 x (σ y)
       grind)
    | (have r₁ := eq167 y (σ x)
       have r₂ := eq58412
       grind)
    | exact resolve eq167 eq58412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq58412
  have eq58814 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq58787
  have eq58815 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq58814
  have eq58826 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq58815
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq58815
    | exact resolve eq58815 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58815
  have eq58835 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq58826
       grind)
    | exact superpose eq58826 eq10
    | exact resolve eq10 eq58826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58826
  have eq58987 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq58835
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58835
    | exact resolve eq58835 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58835
  have eq58990 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 y X0 x
       have i₂ := eq58987
       grind)
    | exact superpose eq58987 eq105
    | exact resolve eq105 eq58987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58987
  have eq59017 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq58990 X0 x
       have i₂ := eq105 x x X0 x
       grind)
    | exact superpose eq105 eq58990
    | exact resolve eq58990 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58990
  have eq273913 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (σ (k X1 (τ X0)))) ∨ (σ X0) = (σ (σ X1)) ∨ (σ X0) = (σ (σ (k X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52640 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52640
    | exact resolve eq52640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52640
  have eq274140 : ∀ X0 X1 : G, (σ (k (σ X1) X0)) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) ∨ (σ X0) = (σ (σ (k X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq273913 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq273913
    | (have j0 := eq273913 X0 X1
       grind)
    | exact resolve eq273913 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273913
  have eq274186 : ∀ X0 X1 : G, (σ (k (σ X1) X0)) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (k (σ X1) X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274140 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq274140
    | (have j0 := eq274140 X0 X1
       grind)
    | exact resolve eq274140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq274140
  have eq274222 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq274186 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq274186
    | exact resolve eq274186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274186
  have eq274525 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274222 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq274222
    | (have j0 := eq274222 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq274222 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq274222
  have eq274775 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274525 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq274525
    | (have j0 := eq274525 X0 X1
       grind)
    | exact resolve eq274525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274525
  have eq274830 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274775 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq274775
    | (have j0 := eq274775 X0 X1
       grind)
    | exact resolve eq274775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274775
  have eq274880 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274830 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq274830
    | (have j0 := eq274830 X0 X1
       grind)
    | exact resolve eq274830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274830
  have eq274918 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274880 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq274880
    | (have j0 := eq274880 X0 X1
       grind)
    | exact resolve eq274880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274880
  have eq274947 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274918 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq274918
    | (have j0 := eq274918 X0 X1
       grind)
    | exact resolve eq274918 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274918
  have eq274972 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq274947 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq274947
    | (have j0 := eq274947 X0 X1
       grind)
    | exact resolve eq274947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274947
  have eq274993 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq274972 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq274972
    | (have j0 := eq274972 X0 X1
       grind)
    | exact resolve eq274972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274972
  have eq275300 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq274993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274993
  have eq353719 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have j0 := eq58125 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58125
  have eq353720 : y = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq353719
  have eq353732 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59017 x
       have i₂ := eq353720
       grind)
    | exact superpose eq353720 eq59017
    | exact resolve eq59017 eq353720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353720
  have eq353788 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by grind
  clear eq353732
  have eq378758 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have j0 := eq58197 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58197
  have eq378759 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq378758
  have eq378785 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq275300 x y
       grind)
    | (have r₁ := eq378759
       have r₂ := eq275300 x y
       grind)
    | exact resolve eq378759 eq275300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275300 eq378759
  have eq378797 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq546 x y
       have i₂ := eq378785
       grind)
    | exact superpose eq378785 eq546
    | (have j0 := eq546 x y
       grind)
    | exact resolve eq546 eq378785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378801 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41197 x y
       have i₂ := eq378785
       grind)
    | exact superpose eq378785 eq41197
    | (have j0 := eq41197 x y
       grind)
    | exact resolve eq41197 eq378785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41197 eq378785
  have eq378802 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq378801
  have eq378804 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq378797
  have eq378811 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq378802
       have i₂ := eq353788
       grind)
    | exact superpose eq353788 eq378802
    | exact resolve eq378802 eq353788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378802
  have eq378812 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by grind
  clear eq378811
  have eq378813 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by grind
  clear eq378812
  have eq378818 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq378813
       grind)
    | exact superpose eq378813 eq16
    | exact resolve eq16 eq378813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378813
  have eq378955 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq59017 eq378818
    | exact resolve eq378818 eq59017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59017 eq378818
  have eq378982 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq353788 eq378955
    | exact resolve eq378955 eq353788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353788 eq378955
  have eq378983 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq378982
  have eq379011 : x = (M.op y x) ∨ (M.op y y) = (M.op y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq378983
       grind)
    | exact superpose eq378983 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq378983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379012 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq546 y x
       have i₂ := eq378983
       grind)
    | exact superpose eq378983 eq546
    | (have j0 := eq546 y x
       grind)
    | exact resolve eq546 eq378983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq378983
  have eq379019 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq379012
  have eq379020 : (M.op y y) = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq379011
  have eq379191 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 y X0 y
       have i₂ := eq379020
       grind)
    | exact superpose eq379020 eq105
    | exact resolve eq105 eq379020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379020
  have eq379242 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq379191 X0 x
       have i₂ := eq105 x x X0 y
       grind)
    | exact superpose eq105 eq379191
    | exact resolve eq379191 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379191
  have eq380081 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq378804
       grind)
    | exact superpose eq378804 eq16
    | exact resolve eq16 eq378804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380231 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq380081
       have i₂ := eq379242 x
       grind)
    | exact superpose eq379242 eq380081
    | exact resolve eq380081 eq379242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380232 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq380081
       have i₂ := eq58111 x
       grind)
    | exact superpose eq58111 eq380081
    | exact resolve eq380081 eq58111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380081
  have eq380233 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq380232
  have eq380234 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq380233
  have eq380235 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq380231
  have eq380236 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq380235
  have eq380243 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq380234
       grind)
    | exact superpose eq380234 eq16
    | exact resolve eq16 eq380234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380265 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (σ y) X0 (σ x)
       have i₂ := eq380234
       grind)
    | exact superpose eq380234 eq105
    | exact resolve eq105 eq380234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380381 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58111 eq380243
    | exact resolve eq380243 eq58111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380243
  have eq380436 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq380236
       grind)
    | exact superpose eq380236 eq16
    | exact resolve eq16 eq380236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380572 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq379242 eq380436
    | exact resolve eq380436 eq379242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379242 eq380436
  have eq387365 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y y)) X1)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (σ x) X0 (σ y)
       have i₂ := eq379019
       grind)
    | exact superpose eq379019 eq105
    | exact resolve eq105 eq379019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379019
  have eq387453 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq387365 X0 x
       have i₂ := eq106 y X0 x
       grind)
    | exact superpose eq106 eq387365
    | exact resolve eq387365 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq387365
  have eq387927 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq380234
       have i₂ := eq387453 (σ x)
       grind)
    | exact superpose eq387453 eq380234
    | exact resolve eq380234 eq387453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380234 eq387453
  have eq388071 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq387927
  have eq388104 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq388071
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq388071
    | exact resolve eq388071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388071
  have eq388464 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq388104
       have r₂ := eq380381
       grind)
    | exact resolve eq388104 eq380381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380381 eq388104
  have eq389033 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq380265 X0 (σ x)
       have i₂ := eq388464
       grind)
    | exact superpose eq388464 eq380265
    | exact resolve eq380265 eq388464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380265 eq388464
  have eq389098 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq389033 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389033
  have eq389759 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq389098 (σ x)
       grind)
    | exact superpose eq389098 eq16
    | exact resolve eq16 eq389098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389098
  have eq389928 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq389759
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq389759
    | exact resolve eq389759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389759
  have eq390317 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58111 eq389928
    | exact resolve eq389928 eq58111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58111 eq389928
  have eq390318 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq390317
  have eq391116 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq390318 eq57671
    | exact resolve eq57671 eq390318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57671
  have eq391121 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 y X0 x
       have i₂ := eq390318
       grind)
    | exact superpose eq390318 eq105
    | exact resolve eq105 eq390318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq391181 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq380236
       have i₂ := eq391116
       grind)
    | exact superpose eq391116 eq380236
    | exact resolve eq380236 eq391116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380236 eq391116
  have eq391267 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq391181
  have eq391303 : y = (M.op x x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq391267
       have r₂ := eq380572
       grind)
    | exact resolve eq391267 eq380572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391267
  have eq392590 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq391303 eq380572
    | exact resolve eq380572 eq391303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380572 eq391303
  have eq392813 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq392590
  have eq393020 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq391121 X0 x
       have i₂ := eq392813
       grind)
    | exact superpose eq392813 eq391121
    | exact resolve eq391121 eq392813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391121 eq392813
  have eq393073 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq393020 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393020
  have eq394489 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq390318
       have i₂ := eq393073 x
       grind)
    | exact superpose eq393073 eq390318
    | exact resolve eq390318 eq393073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393073
  have eq394490 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq394489
  have eq395057 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq394490 eq378804
    | exact resolve eq378804 eq394490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378804 eq394490
  have eq395279 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq395057
  have eq395708 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq395279
       grind)
    | exact superpose eq395279 eq16
    | exact resolve eq16 eq395279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395279
  have eq395848 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq390318 eq395708
    | exact resolve eq395708 eq390318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390318 eq395708
  have eq395849 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq395848
  have eq395973 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq395849
       grind)
    | exact superpose eq395849 eq10
    | exact resolve eq10 eq395849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395849
  have eq396219 : x = y ∨ x = y := by
    first
    | (have i₁ := eq395973
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq395973
    | exact resolve eq395973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395973
  have eq396220 : x = y := by grind
  clear eq396219
  have eq396223 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq396220
       grind)
    | exact superpose eq396220 eq16
    | exact resolve eq16 eq396220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396220
  have eq396224 : False := by grind
  exact eq396224

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k (σ X0) X1)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq294 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 x y
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 x y
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq294
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq294
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq294
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq294
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1599 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1598
  have eq1774 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq302
    | (have j0 := eq302 (τ X1) (τ X0)
       grind)
    | exact resolve eq302 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq302
  have eq1803 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1774 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1774
    | (have j0 := eq1774 X0 X1
       grind)
    | exact resolve eq1774 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq1817 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1803 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1803
    | (have j0 := eq1803 X0 X1
       grind)
    | exact resolve eq1803 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1828 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1817 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1817
    | (have j0 := eq1817 X0 X1
       grind)
    | exact resolve eq1817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq1832 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1828
    | (have j0 := eq1828 X0 X1
       grind)
    | exact resolve eq1828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1835 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1832 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1832
    | (have j0 := eq1832 X0 X1
       grind)
    | exact resolve eq1832 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1832
  have eq1837 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1835 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1835
    | (have j0 := eq1835 X0 X1
       grind)
    | exact resolve eq1835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1838 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1837 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1837
    | (have j0 := eq1837 X0 X1
       grind)
    | exact resolve eq1837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq22936 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1599
       grind)
    | exact superpose eq1599 eq16
    | exact resolve eq16 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq22937 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22936
       have r₂ := eq22 x
       grind)
    | exact resolve eq22936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22936
  have eq22941 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61 y (σ x)
       have i₂ := eq22937
       grind)
    | exact superpose eq22937 eq61
    | (have j0 := eq61 y (σ x)
       grind)
    | (have r₁ := eq61 y (σ x)
       have r₂ := eq22937
       grind)
    | exact resolve eq61 eq22937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq22937
  have eq22959 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq22941
  have eq22960 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq22959
  have eq22967 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq22960
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22960
    | exact resolve eq22960 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22960
  have eq23286 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22967
       grind)
    | exact superpose eq22967 eq10
    | exact resolve eq10 eq22967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22967
  have eq23366 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23286
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23286
    | exact resolve eq23286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23286
  have eq23368 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23366
       grind)
    | exact superpose eq23366 eq16
    | exact resolve eq16 eq23366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23366
  have eq23369 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq23368
       have r₂ := eq22 x
       grind)
    | exact resolve eq23368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23368
  have eq23685 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq23369
       grind)
    | exact superpose eq23369 eq10
    | exact resolve eq10 eq23369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23369
  have eq23771 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23685
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq23685
    | exact resolve eq23685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23685
  have eq23779 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1838 y x
       have i₂ := eq23771
       grind)
    | exact superpose eq23771 eq1838
    | (have j0 := eq1838 y x
       grind)
    | (have r₁ := eq1838 y x
       have r₂ := eq23771
       grind)
    | exact resolve eq1838 eq23771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq23771
  have eq23788 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq23779
  have eq23789 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq23788
  have eq24089 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23789
       grind)
    | exact superpose eq23789 eq16
    | exact resolve eq16 eq23789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23789
  have eq24090 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq24089
       have r₂ := eq22 x
       grind)
    | exact resolve eq24089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24089
  have eq24091 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq24090
       grind)
    | exact superpose eq24090 eq13
    | (have j0 := eq13 (M.op x y) (k y X0)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24090
       grind)
    | exact resolve eq13 eq24090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27301 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have j0 := eq24091 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24091
  have eq27305 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq294
       have i₂ := eq27301
       grind)
    | exact superpose eq27301 eq294
    | exact resolve eq294 eq27301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq27301
  have eq27313 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27305
  have eq27318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27313
       have i₂ := eq24090
       grind)
    | exact superpose eq24090 eq27313
    | exact resolve eq27313 eq24090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24090 eq27313
  have eq27320 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq27318
       have r₂ := eq16
       grind)
    | exact resolve eq27318 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27318
  have eq27511 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27320
       grind)
    | exact superpose eq27320 eq16
    | exact resolve eq16 eq27320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27320
  have eq27519 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq27511
       have r₂ := eq22 x
       grind)
    | exact resolve eq27511 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27511
  have eq27520 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27519
       grind)
    | exact superpose eq27519 eq16
    | exact resolve eq16 eq27519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27521 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27519
       grind)
    | exact superpose eq27519 eq10
    | exact resolve eq10 eq27519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27519
  have eq27617 : x = y := by
    first
    | (have i₁ := eq27521
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27521
    | exact resolve eq27521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27521
  have eq27618 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27520
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq27520
    | exact resolve eq27520 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27520
  have eq27623 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27618
       have i₂ := eq27617
       grind)
    | exact superpose eq27617 eq27618
    | exact resolve eq27618 eq27617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27617 eq27618
  have eq27624 : False := by grind
  exact eq27624

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq95 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq282 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq298 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq307 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq298
    | (have j0 := eq298 X0 X1
       grind)
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq447 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq308
    | exact resolve eq308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308 x y
       grind)
    | exact superpose eq308 eq16
    | (have j1 := eq308 x y
       grind)
    | exact resolve eq16 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq471 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq447
  have eq511 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq471
    | exact resolve eq471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq615 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq453
       have i₂ := eq511 x y
       grind)
    | exact superpose eq511 eq453
    | (have j1 := eq511 (σ x) (σ y)
       grind)
    | (have r₁ := eq453
       have r₂ := eq511 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq453
       have r₂ := eq511 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq453 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq511
  have eq618 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq615
  have eq657 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq618
       grind)
    | exact superpose eq618 eq10
    | exact resolve eq10 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq690 : x = y ∨ x = y := by
    first
    | (have i₁ := eq657
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq657
    | exact resolve eq657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq691 : x = y := by grind
  clear eq690
  have eq693 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq694 : False := by grind
  exact eq694

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X2 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq105
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X2 (τ X0) X1 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq105
    | exact resolve eq105 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq106
    | exact resolve eq106 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq502 : ∀ X0 X1 : G, (M.op X1 (σ (τ (M.op X0 X0)))) = (M.op X1 (σ (M.op (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (τ (M.op X0 X0)) X1
       have i₂ := eq107 X0 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ (M.op X0 X0))
       grind)
    | exact superpose eq107 eq126
    | exact resolve eq126 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq126
  have eq519 : ∀ X0 X1 : G, (M.op X1 (σ (τ (M.op X0 X0)))) = (M.op X1 (σ (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X1
       have i₂ := eq63 (M.op X0 X0)
       grind)
    | exact superpose eq63 eq502
    | exact resolve eq502 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq502
  have eq531 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)))) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq519
    | exact resolve eq519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq170 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq170
    | (have j0 := eq170 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq170 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5178 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (σ (M.op (τ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1)) (τ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq531 (M.op X0 X1) X2
       have i₂ := eq105 (M.op X0 X1) X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact superpose eq105 eq531
    | exact resolve eq531 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq5298 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (σ (M.op (τ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1)) (τ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5178 X0 X1 X2
       have i₂ := eq105 (M.op X0 X1) X1 X2 X0
       grind)
    | exact superpose eq105 eq5178
    | exact resolve eq5178 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178
  have eq10977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq535 x y
       grind)
    | exact superpose eq535 eq16
    | (have j1 := eq535 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq535 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq535 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq535 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq11014 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq10977
  have eq11056 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11014
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11014
       grind)
    | exact resolve eq13 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11057 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (σ x) X0 (σ y)
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq105
    | exact resolve eq105 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11068 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq11056
  have eq11069 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq11068
  have eq11081 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11069
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11069
    | exact resolve eq11069 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq11089 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11081
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11081
    | exact resolve eq11081 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11081
  have eq11091 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14 eq11089
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq11089 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11089
  have eq11092 : (M.op x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq11091
       grind)
    | exact superpose eq11091 eq10
    | exact resolve eq10 eq11091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11091
  have eq11227 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11092
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq11092
    | exact resolve eq11092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11092
  have eq11229 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 y X0 x
       have i₂ := eq11227
       grind)
    | exact superpose eq11227 eq105
    | exact resolve eq105 eq11227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11227
  have eq11240 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11229 X0 x
       have i₂ := eq105 x x X0 x
       grind)
    | exact superpose eq105 eq11229
    | exact resolve eq11229 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11229
  have eq27446 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11057 X0 (σ x)
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq11057
    | exact resolve eq11057 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014 eq11057
  have eq27650 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq27446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27446
  have eq27895 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq27650 (σ x)
       grind)
    | exact superpose eq27650 eq16
    | exact resolve eq16 eq27650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27650
  have eq27929 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq27895
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq27895
    | exact resolve eq27895 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27895
  have eq28021 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11240 eq27929
    | exact resolve eq27929 eq11240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11240 eq27929
  have eq28022 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq28021
  have eq28177 : y ≠ y ∨ x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq28022
       grind)
    | exact superpose eq28022 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq28022
       grind)
    | exact resolve eq13 eq28022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28178 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 x X0 y
       have i₂ := eq28022
       grind)
    | exact superpose eq28022 eq105
    | exact resolve eq105 eq28022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq28197 : y ≠ y ∨ x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq28177
  have eq28198 : (M.op x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq28197
  have eq28200 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170 y x
       have i₂ := eq28198
       grind)
    | exact superpose eq28198 eq170
    | (have j0 := eq170 y x
       grind)
    | exact resolve eq170 eq28198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq28198
  have eq28203 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq28200
  have eq28205 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq28178 X0 x
       have i₂ := eq28022
       grind)
    | exact superpose eq28022 eq28178
    | exact resolve eq28178 eq28022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28178
  have eq28407 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq28205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28205
  have eq130189 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq28203
       grind)
    | exact superpose eq28203 eq16
    | exact resolve eq16 eq28203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28203
  have eq130267 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28407 eq130189
    | exact resolve eq130189 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130189
  have eq130268 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq130267
  have eq130322 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) (τ (σ y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5298 (σ y) (σ x) x
       have i₂ := eq130268
       grind)
    | exact superpose eq130268 eq5298
    | exact resolve eq5298 eq130268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5298
  have eq130350 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130322 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq130322
    | exact resolve eq130322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130322
  have eq130373 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (M.op (σ (M.op y y)) (σ x))) y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130350 X0
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq130350
    | exact resolve eq130350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130350
  have eq130390 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (M.op (σ (M.op y y)) (σ x))) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28407 eq130373
    | exact resolve eq130373 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130373
  have eq130404 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (M.op (σ (M.op y x)) (σ x))) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28407 eq130390
    | exact resolve eq130390 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130390
  have eq130414 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (M.op (σ y) (σ x))) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28022 eq130404
    | exact resolve eq130404 eq28022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130404
  have eq130423 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op (τ (σ y)) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq130268 eq130414
    | exact resolve eq130414 eq130268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130268 eq130414
  have eq130429 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130423 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq130423
    | exact resolve eq130423 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130423
  have eq130435 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28022 eq130429
    | exact resolve eq130429 eq28022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28022 eq130429
  have eq130653 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq130435 (σ x)
       grind)
    | exact superpose eq130435 eq16
    | exact resolve eq16 eq130435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130435
  have eq130756 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130653
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq130653
    | exact resolve eq130653 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130653
  have eq130952 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28407 eq130756
    | exact resolve eq130756 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28407 eq130756
  have eq130953 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq130952
  have eq131495 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq130953
       grind)
    | exact superpose eq130953 eq10
    | exact resolve eq10 eq130953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130953
  have eq131678 : x = y ∨ x = y := by
    first
    | (have i₁ := eq131495
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq131495
    | exact resolve eq131495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131495
  have eq131679 : x = y := by grind
  clear eq131678
  have eq131682 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131679
       grind)
    | exact superpose eq131679 eq16
    | exact resolve eq16 eq131679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131679
  have eq131683 : False := by grind
  exact eq131683
