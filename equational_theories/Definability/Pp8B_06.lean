import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxy_pyx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq66
    | exact resolve eq66 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq66
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq10
    | exact resolve eq10 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | (have j0 := eq96 (τ X0) X1
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq482 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq459
    | (have j0 := eq459 X0 X1
       grind)
    | exact resolve eq459 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq459
  have eq488 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq482 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq482 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq492 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq488 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq488
    | (have j0 := eq488 X0 X1
       grind)
    | exact resolve eq488 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq576 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X2 X0
       have i₂ := eq136 X1 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1 X0
       have i₂ := eq136 X0 X1 X0
       grind)
    | exact superpose eq136 eq19
    | exact resolve eq19 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq136 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq136 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq136 eq9
    | exact resolve eq9 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq777 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op X0 X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq576 X3 (M.op X0 X1) (M.op X2 X0)
       have i₂ := eq611 X0 X1 X2
       grind)
    | exact superpose eq611 eq576
    | exact resolve eq576 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq782 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq611 X0 x X1
       grind)
    | exact superpose eq611 eq9
    | exact resolve eq9 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq782 (σ X0) (σ X0) x
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq782
    | exact resolve eq782 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq1027 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f1027_12 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
      intro X0 X1
      grind
    have f1027_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f1027_22 : (σ X0) ≠ (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by grind
    have f1027_49 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
      intro X0 X1
      first
      | (have i₁ := f1027_12 (M.op x (M.op x x)) X1
         have i₂ := f1027_14 x (M.op x x) x
         grind)
      | exact superpose f1027_14 f1027_12
      | exact resolve f1027_12 f1027_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1027_253 : (σ X0) ≠ (σ X0) := by
      first
      | (have i₁ := f1027_22
         have i₂ := f1027_49 X0 X1
         grind)
      | exact superpose f1027_49 f1027_22
      | (have r₁ := f1027_22
         have r₂ := f1027_49 X0 X1
         grind)
      | exact resolve f1027_22 f1027_49
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1027_258 : False := by grind
    exact f1027_258
  clear eq823
  have eq1082 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq492
    | (have j0 := eq492 X1 (τ X0)
       grind)
    | exact resolve eq492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq492 (σ X1) X0
       grind)
    | exact superpose eq492 eq15
    | (have j1 := eq492 (σ X1) X0
       grind)
    | exact resolve eq15 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq1103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1089 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq1089
    | (have j0 := eq1089 X0 X1
       grind)
    | exact resolve eq1089 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1108 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1082 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq1082
    | (have j0 := eq1082 X0 X1
       grind)
    | exact resolve eq1082 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1082
  have eq1129 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1108 (τ X0) X1
       grind)
    | exact superpose eq1108 eq17
    | (have j1 := eq1108 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1108
  have eq1136 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1129 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq1129
    | (have j0 := eq1129 X0 X1
       grind)
    | exact resolve eq1129 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1129
  have eq1261 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (M.op X0 (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq1027 X0 X1
       grind)
    | exact superpose eq1027 eq82
    | exact resolve eq82 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1027
  have eq1284 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1261 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq1261
    | exact resolve eq1261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1290 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1284 X0 x
       have i₂ := eq135 (σ X0) (σ X0) x
       grind)
    | exact superpose eq135 eq1284
    | exact resolve eq1284 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1284
  have eq1292 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1290 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq1290
    | exact resolve eq1290 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq5190 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) = (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1292 (M.op x x)
       have i₂ := eq777 x x x x
       grind)
    | (have i₁ := eq1292 (M.op x x)
       have i₂ := eq777 x x x x
       grind)
    | exact superpose eq777 eq1292
    | exact resolve eq1292 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq5235 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5190 X0 X1
       have i₂ := eq611 X0 X0 X1
       grind)
    | exact superpose eq611 eq5190
    | exact resolve eq5190 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190
  have eq26881 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1103 x y
       grind)
    | exact superpose eq1103 eq16
    | (have j1 := eq1103 x y
       grind)
    | exact resolve eq16 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq56271 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1136 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1136
    | (have j0 := eq1136 (σ X0) X1
       grind)
    | exact resolve eq1136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq56544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56271 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56271
    | (have j0 := eq56271 X0 X1
       grind)
    | exact resolve eq56271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56271
  have eq56575 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56544 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq56544
    | (have j0 := eq56544 X0 X1
       grind)
    | exact resolve eq56544 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56544
  have eq56595 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56575 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq56575
    | (have j0 := eq56575 X0 X1
       grind)
    | exact resolve eq56575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56575
  have eq61962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq26881
       have i₂ := eq56595 x y
       grind)
    | exact superpose eq56595 eq26881
    | (have j1 := eq56595 x y
       grind)
    | (have r₁ := eq26881
       have r₂ := eq56595 x y
       grind)
    | exact resolve eq26881 eq56595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26881 eq56595
  have eq61965 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq61962
  have eq62843 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq61965
       grind)
    | exact superpose eq61965 eq10
    | exact resolve eq10 eq61965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61965
  have eq62954 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq62843
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq62843
    | exact resolve eq62843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62843
  have eq62955 : (M.op x x) = (M.op y y) := by grind
  clear eq62954
  have eq63135 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op (M.op x x) (M.op x x)))) := by
    first
    | (have i₁ := eq5235 y y
       have i₂ := eq62955
       grind)
    | exact superpose eq62955 eq5235
    | exact resolve eq5235 eq62955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5235 eq62955
  have eq63153 : (σ y) = (σ (M.op (M.op x x) (M.op (M.op x x) (M.op x x)))) := by
    first
    | (have i₁ := eq63135
       have i₂ := eq1292 (M.op x x)
       grind)
    | exact superpose eq1292 eq63135
    | exact resolve eq63135 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292 eq63135
  have eq63189 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63153
       have i₂ := eq611 x x x
       grind)
    | exact superpose eq611 eq63153
    | exact resolve eq63153 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq63153
  have eq64272 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63189
       grind)
    | exact superpose eq63189 eq16
    | exact resolve eq16 eq63189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64273 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq63189
       grind)
    | exact superpose eq63189 eq10
    | exact resolve eq10 eq63189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63189
  have eq64422 : x = y := by
    first
    | (have i₁ := eq64273
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64273
    | exact resolve eq64273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64273
  have eq64423 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq64272
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq64272
    | exact resolve eq64272 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq64272
  have eq64432 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq64423
       have i₂ := eq64422
       grind)
    | exact superpose eq64422 eq64423
    | exact resolve eq64423 eq64422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64422 eq64423
  have eq64433 : False := by grind
  exact eq64433

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq208 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq195
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208
    | (have j0 := eq208 X0
       grind)
    | exact resolve eq208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq210 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq210 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq211 (σ X0)
       grind)
    | exact superpose eq211 eq15
    | exact resolve eq15 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq218
    | exact resolve eq218 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq360 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1289 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1326 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1289 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1289
    | (have j0 := eq1289 X0 X1
       grind)
    | exact resolve eq1289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq360
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq360
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq360
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq360
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq360 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1961 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq1960
  have eq52581 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1961
       grind)
    | exact superpose eq1961 eq16
    | exact resolve eq16 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq52582 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq52581
       have r₂ := eq225 x
       grind)
    | exact resolve eq52581 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52581
  have eq65489 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52582
       grind)
    | exact superpose eq52582 eq10
    | exact resolve eq10 eq52582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52582
  have eq65590 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65489
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65489
    | exact resolve eq65489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65489
  have eq65872 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65590
       grind)
    | exact superpose eq65590 eq16
    | exact resolve eq16 eq65590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65590
  have eq65873 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq65872
       have r₂ := eq225 x
       grind)
    | exact resolve eq65872 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65872
  have eq65878 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq65873
       grind)
    | exact superpose eq65873 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq65873
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq65873
       grind)
    | exact resolve eq12 eq65873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65873
  have eq65983 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq65878
  have eq67123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq360
       have i₂ := eq65983
       grind)
    | exact superpose eq65983 eq360
    | exact resolve eq360 eq65983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq65983
  have eq67136 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq67123
  have eq67137 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq67136
  have eq68258 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67137
       grind)
    | exact superpose eq67137 eq10
    | exact resolve eq10 eq67137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67137
  have eq68363 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq68258
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68258
    | exact resolve eq68258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68258
  have eq68379 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68363
       grind)
    | exact superpose eq68363 eq16
    | exact resolve eq16 eq68363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68363
  have eq68384 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq68379
       have r₂ := eq225 x
       grind)
    | exact resolve eq68379 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq68379
  have eq69893 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq68384
       grind)
    | exact superpose eq68384 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq68384
       grind)
    | exact resolve eq12 eq68384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68384
  have eq70002 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq69893
  have eq70064 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq70002
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq70002
    | exact resolve eq70002 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70002
  have eq74703 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70064
       grind)
    | exact superpose eq70064 eq16
    | exact resolve eq16 eq70064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70064
  have eq74973 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74703
       have i₂ := eq1326 y x
       grind)
    | exact superpose eq1326 eq74703
    | (have j1 := eq1326 x y
       grind)
    | (have r₁ := eq74703
       have r₂ := eq1326 y x
       grind)
    | (have r₁ := eq74703
       have r₂ := eq1326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq74703
       have r₂ := eq1326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq74703 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq74974 : x = y ∨ x = (M.op y x) := by grind
  clear eq74973
  have eq75359 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74703
       have i₂ := eq74974
       grind)
    | exact superpose eq74974 eq74703
    | exact resolve eq74703 eq74974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74974
  have eq75360 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75359
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq75359
    | exact resolve eq75359 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq75359
  have eq75361 : x = (M.op y x) := by grind
  clear eq75360
  have eq75374 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq75361
       grind)
    | exact superpose eq75361 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq75361
       grind)
    | exact resolve eq12 eq75361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75361
  have eq75484 : (M.op x y) = (k x y) := by grind
  clear eq75374
  have eq76106 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq74703
       have i₂ := eq75484
       grind)
    | exact superpose eq75484 eq74703
    | exact resolve eq74703 eq75484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74703 eq75484
  have eq76115 : False := by grind
  exact eq76115

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq51
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq55 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq55
  have eq163 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq168 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       have j1 := eq59 X1 X0
       grind)
    | (have r₁ := eq163 X1 X0
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq163 X1 X1
       have r₂ := eq59 X1 X1
       grind)
    | exact resolve eq163 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq163
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq168 (σ X1) (σ X0)
       grind)
    | exact superpose eq168 eq15
    | exact resolve eq15 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq168 X1 X0
       grind)
    | exact superpose eq168 eq223
    | exact resolve eq223 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq223
  have eq230 : False := by grind
  exact eq230

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) := by
    intro X0 X1
    grind
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X2 X1))) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X0) = (k X2 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X0) (k (M.op X0 X0) X0) (M.op (M.op X0 X0) X1)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq24
    | exact resolve eq24 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq465 X0 x
       have i₂ := eq132 (M.op X0 X0) (M.op X0 X0) x
       grind)
    | exact superpose eq132 eq465
    | exact resolve eq465 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq465
  have eq494 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq487 X0
       have i₂ := eq134 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq134 eq487
    | exact resolve eq487 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq496 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq494 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq494
    | exact resolve eq494 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq504 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq496 X0
       grind)
    | exact superpose eq496 eq37
    | exact resolve eq37 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq849 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X1 (M.op x (M.op x X0))
       have i₂ := eq79 X1 X0 x
       grind)
    | exact superpose eq79 eq504
    | (have j1 := eq79 X1 X0 x
       grind)
    | exact resolve eq504 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq504
  have eq1118 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 X0
       have i₂ := eq134 X1 X2 X0
       grind)
    | (have i₁ := eq24 X0 X1 X0
       have i₂ := eq134 X0 X1 X0
       grind)
    | exact superpose eq134 eq24
    | exact resolve eq24 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq134 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq134 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq134 eq9
    | exact resolve eq9 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1280 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    grind
  clear eq1118
  have eq1352 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1280 X0 X1
       have i₂ := eq496 X0
       grind)
    | exact superpose eq496 eq1280
    | exact resolve eq1280 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1682 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq1164 X0 x X1
       grind)
    | exact superpose eq1164 eq9
    | exact resolve eq9 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1761 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1682 (k (M.op X0 X0) X0) (M.op X0 X0) x
       have i₂ := eq496 X0
       grind)
    | exact superpose eq496 eq1682
    | exact resolve eq1682 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq1682
  have eq6705 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq6706 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6705 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq6705 X1 X1
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq6705 X1 X1
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq6705 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq92 X0 (M.op X1 X1)
       grind)
    | exact resolve eq6705 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq6705
  have eq10972 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1352 X1 X1
       have i₂ := eq6706 X0 X1
       grind)
    | (have i₁ := eq1352 X0 X1
       have i₂ := eq6706 (M.op X1 X0) X1
       grind)
    | exact superpose eq6706 eq1352
    | (have j1 := eq6706 X0 X1
       grind)
    | exact resolve eq1352 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq11029 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6706 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706
  have eq11031 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq10972 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10972
  have eq11042 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11029 X0 X1
       have j1 := eq849 X1 X0
       grind)
    | (have r₁ := eq11029 X1 X1
       have r₂ := eq849 X1 X1
       grind)
    | (have r₁ := eq11029 X1 X0
       have r₂ := eq849 X0 X1
       grind)
    | (have r₁ := eq11029 X0 X1
       have r₂ := eq849 X0 (M.op X1 X0)
       grind)
    | exact resolve eq11029 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq11029
  have eq12128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11031 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11031
  have eq13837 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12128 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12128
  have eq13955 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq13837 (σ X0)
       grind)
    | exact superpose eq13837 eq15
    | exact resolve eq15 eq13837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13970 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13955 X0
       have i₂ := eq13837 X0
       grind)
    | exact superpose eq13837 eq13955
    | exact resolve eq13955 eq13837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13837 eq13955
  have eq14763 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11042 X1 (σ X0)
       have i₂ := eq13970 X0
       grind)
    | exact superpose eq13970 eq11042
    | (have j0 := eq11042 X1 (σ X0)
       grind)
    | exact resolve eq11042 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14804 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1761 (σ X0) (σ X0)
       have i₂ := eq13970 X0
       grind)
    | exact superpose eq13970 eq1761
    | exact resolve eq1761 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq13970
  have eq14811 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq14804 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq14804
    | exact resolve eq14804 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14804
  have eq25408 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (k X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq14811 (M.op x (M.op x x))
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq14811
    | exact resolve eq14811 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14811
  have eq25505 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25408 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq25408
    | exact resolve eq25408 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq25408
  have eq49581 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq14763 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq14763 X0 (σ X0)
       grind)
    | exact superpose eq14763 eq10
    | (have j1 := eq14763 X1 X0
       grind)
    | exact resolve eq10 eq14763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14763
  have eq67054 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq49581 (σ X1) X0
       grind)
    | exact superpose eq49581 eq15
    | (have j1 := eq49581 (σ X1) X0
       grind)
    | exact resolve eq15 eq49581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49581
  have eq67072 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67054 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq67054
    | (have j0 := eq67054 X0 X1
       grind)
    | exact resolve eq67054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67054
  have eq77989 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67072 x y
       grind)
    | exact superpose eq67072 eq16
    | (have j1 := eq67072 x y
       grind)
    | exact resolve eq16 eq67072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67072
  have eq78955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77989
       have i₂ := eq11042 y x
       grind)
    | exact superpose eq11042 eq77989
    | (have j1 := eq11042 y x
       grind)
    | exact resolve eq77989 eq11042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11042 eq77989
  have eq78958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq78955
  have eq78959 : y = (M.op x x) := by grind
  clear eq78958
  have eq79272 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25505 x
       have i₂ := eq78959
       grind)
    | exact superpose eq78959 eq25505
    | exact resolve eq25505 eq78959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25505 eq78959
  have eq79377 : False := by grind
  exact eq79377

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq851 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq11982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11982
    | exact resolve eq11982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11982
  have eq11994 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11983
       have r₂ := eq28
       grind)
    | exact resolve eq11983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11983
  have eq11996 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11994
    | exact resolve eq11994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11994
  have eq12107 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11996
  have eq12135 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12107
    | exact resolve eq12107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12107
  have eq12146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12135 eq115
    | exact resolve eq115 eq12135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12135
  have eq12155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12146
  have eq12157 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12155
       have r₂ := eq28
       grind)
    | exact resolve eq12155 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155
  have eq12174 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12157
  have eq12202 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12174
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12174
    | exact resolve eq12174 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12174
  have eq12210 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq12202
       grind)
    | exact superpose eq12202 eq74
    | exact resolve eq74 eq12202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12202
  have eq12226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12210
    | exact resolve eq12210 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210
  have eq12302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12226 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12302
    | exact resolve eq12302 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12302
  have eq12316 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12305
       have r₂ := eq28
       grind)
    | exact resolve eq12305 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12305
  have eq12318 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12316
    | exact resolve eq12316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12316
  have eq12319 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12318
  have eq12335 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12319
  have eq12363 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12335
    | exact resolve eq12335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12335
  have eq12778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12363 eq12226
    | exact resolve eq12226 eq12363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226 eq12363
  have eq12781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12778
  have eq12785 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12781
       have r₂ := eq28
       grind)
    | exact resolve eq12781 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12781
  have eq12787 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12785 eq28
    | exact resolve eq28 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12790 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12785 eq78
    | (have r₁ := eq78
       have r₂ := eq12785
       grind)
    | exact resolve eq78 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq12822 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12790
  have eq19505 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12822
  have eq19549 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19505
    | exact resolve eq19505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19505
  have eq20549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq19549
    | exact resolve eq19549 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq20571 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19549
  have eq20576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20549
  have eq20578 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20571
       have r₂ := eq12785
       grind)
    | exact resolve eq20571 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12785 eq20571
  have eq20580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20576
       have r₂ := eq12787
       grind)
    | exact resolve eq20576 eq12787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12787 eq20576
  have eq20582 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20580
       have r₂ := eq28
       grind)
    | exact resolve eq20580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20580
  have eq20591 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20578 eq84
    | exact resolve eq84 eq20578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq20578
  have eq20631 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20591
    | exact resolve eq20591 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20591
  have eq20651 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq20582
  have eq20686 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20651
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20651
    | exact resolve eq20651 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20651
  have eq21327 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20631
       have i₂ := eq20686
       grind)
    | exact superpose eq20686 eq20631
    | exact resolve eq20631 eq20686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20631 eq20686
  have eq21336 : x = (M.op x y) := by grind
  clear eq21327
  have eq21375 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21336 eq21
    | exact resolve eq21 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21382 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq21336 eq77
    | (have r₁ := eq77
       have r₂ := eq21336
       grind)
    | exact resolve eq77 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq21460 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq21382
  have eq21511 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21375
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21375
    | exact resolve eq21375 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21375
  have eq21745 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21511 eq27
    | exact resolve eq27 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24286 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq21460
  have eq24327 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq24286
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24286
    | exact resolve eq24286 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24286
  have eq24355 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq21336 eq24327
    | exact resolve eq24327 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21336 eq24327
  have eq24356 : x = (k y x) := by grind
  clear eq24355
  have eq24387 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq24356
       grind)
    | exact superpose eq24356 eq74
    | exact resolve eq74 eq24356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq24403 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq851 x y
       have i₂ := eq24356
       grind)
    | exact superpose eq24356 eq851
    | (have j0 := eq851 x y
       grind)
    | exact resolve eq851 eq24356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq24356
  have eq24404 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq24403
  have eq24411 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24404
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24404
    | exact resolve eq24404 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24404
  have eq24425 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21511 eq24387
    | exact resolve eq24387 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24387
  have eq24427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24411
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24411
    | exact resolve eq24411 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24411
  have eq24439 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq24425
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24425
    | exact resolve eq24425 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24425
  have eq24440 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq24427
    | exact resolve eq24427 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24427
  have eq24451 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21511 eq24439
    | exact resolve eq24439 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24439
  have eq24452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21511 eq24440
    | exact resolve eq24440 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24440
  have eq24458 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq24452
       have r₂ := eq28
       grind)
    | exact resolve eq24452 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24452
  have eq24464 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24458
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24458
    | exact resolve eq24458 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24458
  have eq24470 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21511 eq24464
    | exact resolve eq24464 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21511 eq24464
  have eq24476 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq24470
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24470
    | exact resolve eq24470 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq24470
  have eq24669 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq24476
  have eq24710 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21745 eq24669
    | exact resolve eq24669 eq21745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21745 eq24669
  have eq24718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24451 eq24710
    | exact resolve eq24710 eq24451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24451 eq24710
  have eq24721 : False := by grind
  exact eq24721

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq54 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq54
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq59
  have eq127 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq131 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq127 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | (have r₁ := eq127 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq127 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq127
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq131 (σ X1) (σ X0)
       grind)
    | exact superpose eq131 eq15
    | exact resolve eq15 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq131 X1 X0
       grind)
    | exact superpose eq131 eq263
    | exact resolve eq263 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq263
  have eq269 : False := by grind
  exact eq269

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq43 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq143 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq43 X0 X1 X2
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq501 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108 x y
       grind)
    | exact superpose eq108 eq16
    | (have j1 := eq108 x y
       grind)
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq640 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq143 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq143 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq143 eq9
    | exact resolve eq9 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq896 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq640 X0 x X1
       grind)
    | exact superpose eq640 eq9
    | exact resolve eq9 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq937 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq896 (σ X0) (σ X0) x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq896
    | exact resolve eq896 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1147 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq937 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq937
    | exact resolve eq937 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1335 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq1147 X0 X1
       grind)
    | exact superpose eq1147 eq50
    | exact resolve eq50 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1147
  have eq1356 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq1335
    | exact resolve eq1335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1362 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1356 X0 x
       have i₂ := eq144 (σ X0) (σ X0) x
       grind)
    | exact superpose eq144 eq1356
    | exact resolve eq1356 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq1356
  have eq1364 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1362 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq1362
    | exact resolve eq1362 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq2857 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq501
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq501
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq501
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq501
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq501 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq2858 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2857
  have eq61689 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2858
       grind)
    | exact superpose eq2858 eq16
    | exact resolve eq16 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq61690 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq61689
       have r₂ := eq23 x
       grind)
    | exact resolve eq61689 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61689
  have eq64507 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq61690
       grind)
    | exact superpose eq61690 eq10
    | exact resolve eq10 eq61690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61690
  have eq64601 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq64507
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64507
    | exact resolve eq64507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64507
  have eq64604 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64601
       grind)
    | exact superpose eq64601 eq16
    | exact resolve eq16 eq64601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64601
  have eq64605 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq64604
       have r₂ := eq23 x
       grind)
    | exact resolve eq64604 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq64604
  have eq65114 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq64605
       grind)
    | exact superpose eq64605 eq10
    | exact resolve eq10 eq64605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64605
  have eq65225 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65114
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq65114
    | exact resolve eq65114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65114
  have eq65226 : y = (M.op x x) := by grind
  clear eq65225
  have eq65305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1364 x
       have i₂ := eq65226
       grind)
    | exact superpose eq65226 eq1364
    | exact resolve eq1364 eq65226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq65226
  have eq65469 : False := by grind
  exact eq65469

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxy_x_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 (k X0 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X3 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq428 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq456 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq189
       grind)
    | exact superpose eq189 eq41
    | exact resolve eq41 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq189
  have eq457 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq456
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq456
    | exact resolve eq456 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq459 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq457
    | exact resolve eq457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq459 eq190
    | exact resolve eq190 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq459
  have eq555 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq548
       have r₂ := eq27
       grind)
    | exact resolve eq548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq631 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq555 eq13
    | exact resolve eq13 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq633 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq631
  have eq639 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq635
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq635
    | exact resolve eq635 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq665 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq639 eq98
    | exact resolve eq98 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq639
  have eq672 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq665
    | exact resolve eq665 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq665
  have eq673 : y = (k x x) := by grind
  clear eq672
  have eq679 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq673
       grind)
    | exact superpose eq673 eq40
    | exact resolve eq40 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq682 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq679
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq679
    | exact resolve eq679 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq685 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq682
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq682
    | exact resolve eq682 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1211 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (k x x))) := by
    intro X0
    first
    | (have i₁ := eq175 X0 x
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq175
    | exact resolve eq175 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1214 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq176 X0 sF2
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq176
    | exact resolve eq176 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1279 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq685 eq1214
    | exact resolve eq1214 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1280 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1211 X0
       have i₂ := eq673
       grind)
    | exact superpose eq673 eq1211
    | exact resolve eq1211 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1406 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1280 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1280
    | (have j0 := eq1280 x
       grind)
    | exact resolve eq1280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1280
  have eq1416 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1406
       have i₂ := eq633 sF0
       grind)
    | exact superpose eq633 eq1406
    | exact resolve eq1406 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1420 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1416 eq42
    | exact resolve eq42 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1423 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1420
    | exact resolve eq1420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1420
  have eq1426 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1423
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1423
    | exact resolve eq1423 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq2045 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1279 eq177
    | exact resolve eq177 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1279
  have eq2177 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1426 eq185
    | (have j0 := eq185 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq185 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2242 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2045 eq2177
    | exact resolve eq2177 eq2045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045 eq2177
  have eq2290 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2242 X0
       have i₂ := eq633 sF1
       grind)
    | exact superpose eq633 eq2242
    | (have j0 := eq2242 X0
       grind)
    | exact resolve eq2242 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2298 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1426 eq2290
    | (have j0 := eq2290 X0
       grind)
    | exact resolve eq2290 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq3600 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2298 sF1
       have i₂ := eq633 sF1
       grind)
    | exact superpose eq633 eq2298
    | exact resolve eq2298 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq3640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1426 eq3600
    | exact resolve eq3600 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq3600
  have eq3645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq3640
    | exact resolve eq3640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq3647 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3645
       have r₂ := eq27
       grind)
    | exact resolve eq3645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq3650 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq3647 eq86
    | exact resolve eq86 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq3654 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) := by
    first
    | exact superpose eq3647 eq132
    | exact resolve eq132 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3661 : (k (M.op x y) x) = (k x (τ (σ x))) := by
    first
    | exact superpose eq91 eq3654
    | exact resolve eq3654 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3654
  have eq3664 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq3650 X0
       have i₂ := eq428 X0 sF2
       grind)
    | exact superpose eq428 eq3650
    | exact resolve eq3650 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq3650
  have eq3668 : (k x x) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq3661
    | exact resolve eq3661 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3671 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq3664
    | exact resolve eq3664 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3664
  have eq3674 : y = (k (M.op x y) x) := by
    first
    | (have i₁ := eq3668
       have i₂ := eq673
       grind)
    | exact superpose eq673 eq3668
    | exact resolve eq3668 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq3668
  have eq3677 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3674
       have i₂ := eq3671 sF0
       grind)
    | exact superpose eq3671 eq3674
    | exact resolve eq3674 eq3671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671 eq3674
  have eq3680 : x = y := by
    first
    | exact superpose eq1416 eq3677
    | exact resolve eq3677 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq3677
  have eq3683 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3680
       grind)
    | exact superpose eq3680 eq24
    | exact resolve eq24 eq3680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3680
  have eq3718 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3683
    | exact resolve eq3683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3683
  have eq3809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3718 eq26
    | exact resolve eq26 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3886 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3809
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq3809
    | exact resolve eq3809 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq3809
  have eq3909 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq685 eq3886
    | exact resolve eq3886 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq3886
  have eq3917 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3718 eq3909
    | exact resolve eq3909 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3718 eq3909
  have eq3918 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3917 eq27
    | exact resolve eq27 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3917
  have eq3966 : False := by grind
  exact eq3966
