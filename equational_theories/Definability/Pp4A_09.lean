import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq44
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq44 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq201 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 X2 X2 X2
       have i₂ := eq53 X2 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (k X1 (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X1 X2)
       have i₂ := eq53 X1 X0 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X1)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X1 X2)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq53 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq52 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq617
    | exact resolve eq617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq621 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq618
       have r₂ := eq27
       grind)
    | exact resolve eq618 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq670 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 X2) (M.op (σ (k X0 X1)) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X2 (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq14
    | (have j1 := eq94 X0 X1
       grind)
    | exact resolve eq14 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq688 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq621 eq53
    | exact resolve eq53 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq621 eq14
    | exact resolve eq14 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq690 eq51
    | exact resolve eq51 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq719 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq690 eq204
    | exact resolve eq204 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq727 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq714 eq53
    | exact resolve eq53 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq727
    | (have j0 := eq727 X0
       grind)
    | exact resolve eq727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq739 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq714
    | exact resolve eq714 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq719
  have eq744 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by grind
  clear eq739
  have eq878 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq731 eq688
    | exact resolve eq688 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq731
  have eq887 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq878
  have eq1123 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op X1 X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq379 eq53
    | exact resolve eq53 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq621 eq744
    | exact resolve eq744 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq744
  have eq1132 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1126
  have eq1138 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1132 eq887
    | exact resolve eq887 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq1132
  have eq1168 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1138
  have eq1250 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq376 y x X0
       have i₂ := eq1168
       grind)
    | exact superpose eq1168 eq376
    | exact resolve eq376 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq1254 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq1168
       grind)
    | exact superpose eq1168 eq14
    | exact resolve eq14 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1398 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq363 X3 X1 x
       have i₂ := eq363 X0 X1 x
       grind)
    | (have i₁ := eq363 X0 X1 X3
       have i₂ := eq363 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq363 eq363
    | exact resolve eq363 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1410 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq363 X0 (M.op X1 X1) X3
       have i₂ := eq363 X0 X1 X1
       grind)
    | (have i₁ := eq363 X0 (M.op X1 X1) X3
       have i₂ := eq363 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq363 eq363
    | exact resolve eq363 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq363 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq363 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq363 eq14
    | exact resolve eq14 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq363 X0 X1 X1
       grind)
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq363 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq363 eq50
    | exact resolve eq50 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (M.op X1 X1)
       have i₂ := eq363 X0 X1 X1
       grind)
    | (have i₁ := eq201 (M.op X1 X1)
       have i₂ := eq363 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq363 eq201
    | exact resolve eq201 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1506 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1410 X0 X1 x X3
       have i₂ := eq52 X0 x X1
       grind)
    | exact superpose eq52 eq1410
    | exact resolve eq1410 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1410
  have eq2298 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1254 x
       have i₂ := eq363 X0 y x
       grind)
    | (have i₁ := eq1254 X0
       have i₂ := eq363 (M.op X0 X0) y x
       grind)
    | exact superpose eq363 eq1254
    | exact resolve eq1254 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2318 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op y y) X1
       have i₂ := eq1254 y
       grind)
    | exact superpose eq1254 eq14
    | exact resolve eq14 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : x = (M.op y (M.op (M.op x y) x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 (M.op y y)
       have i₂ := eq1254 y
       grind)
    | exact superpose eq1254 eq50
    | exact resolve eq50 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2325 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq201 (M.op y y)
       have i₂ := eq1254 y
       grind)
    | exact superpose eq1254 eq201
    | exact resolve eq201 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq2331 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op y X1)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq383 (M.op y y) X1 X0
       have i₂ := eq1254 y
       grind)
    | exact superpose eq1254 eq383
    | exact resolve eq383 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2441 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2319 eq1250
    | exact resolve eq1250 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq2447 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2441
  have eq2452 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2447
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2447
    | exact resolve eq2447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2730 : x = (M.op y (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2325 eq2319
    | exact resolve eq2319 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq2325
  have eq2736 : x = (M.op y (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2730
  have eq2971 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2736
       have i₂ := eq1168
       grind)
    | exact superpose eq1168 eq2736
    | exact resolve eq2736 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq2736
  have eq2981 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2971
  have eq3076 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2452
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq2452
    | exact resolve eq2452 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3077 : ∀ X0 : G, y = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2298 X0
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq2298
    | exact resolve eq2298 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3087 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 y X1
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq53
    | exact resolve eq53 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3115 : ∀ X0 : G, y = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3077 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq3116 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3076
  have eq3421 : ∀ X0 : G, x = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq3115 sF0
       grind)
    | exact superpose eq3115 eq378
    | exact resolve eq378 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq3115
  have eq3568 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq379 eq377
    | exact resolve eq377 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq379
  have eq7471 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq670 y x X0
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq670
    | (have j0 := eq670 y x x
       grind)
    | exact resolve eq670 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq7562 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7471 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7471
    | (have j0 := eq7471 X0
       grind)
    | exact resolve eq7471 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7471
  have eq7598 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7562 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7562
    | (have j0 := eq7562 X0
       grind)
    | exact resolve eq7562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7562
  have eq7627 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7598 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7598
    | (have j0 := eq7598 X0
       grind)
    | exact resolve eq7598 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq7648 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq7627
    | (have j0 := eq7627 X0
       grind)
    | exact resolve eq7627 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7627
  have eq8420 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq389 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq8421 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8420 X0
       have i₂ := eq383 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq383 eq8420
    | (have j0 := eq8420 X0
       grind)
    | exact resolve eq8420 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8420
  have eq9045 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X2 (M.op X0 (M.op X1 X1))) = (k X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq455 X1 X1
       have i₂ := eq363 X0 X1 X1
       grind)
    | (have i₁ := eq455 X1 X1
       have i₂ := eq363 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq363 eq455
    | exact resolve eq455 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq455
  have eq10816 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2318 X0 (M.op y y)
       have i₂ := eq2298 X0
       grind)
    | exact superpose eq2298 eq2318
    | exact resolve eq2318 eq2298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq11047 : ∀ X0 : G, x = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3421 (M.op (M.op X0 x) X0)
       have i₂ := eq2318 X0 x
       grind)
    | exact superpose eq2318 eq3421
    | exact resolve eq3421 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq11064 : ∀ X0 : G, x = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11047
  have eq11146 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10816
  have eq11370 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2318 X0 y
       have i₂ := eq11064 X0
       grind)
    | exact superpose eq11064 eq2318
    | exact resolve eq2318 eq11064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq11064
  have eq11431 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11370
  have eq12975 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11146 (M.op x X0)
       have i₂ := eq11431 X0
       grind)
    | exact superpose eq11431 eq11146
    | exact resolve eq11146 eq11431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11146 eq11431
  have eq12999 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12975 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975
  have eq15227 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2331 y X0
       have i₂ := eq2452
       grind)
    | exact superpose eq2452 eq2331
    | exact resolve eq2331 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq2452
  have eq15429 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15227
  have eq15451 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15429 X0
       have i₂ := eq12999 X0
       grind)
    | exact superpose eq12999 eq15429
    | exact resolve eq15429 eq12999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12999 eq15429
  have eq15551 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15451
  have eq49226 : (σ y) = (M.op x (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7648 y
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq7648
    | exact resolve eq7648 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7648
  have eq49382 : (σ y) = (M.op x (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq49226
  have eq87516 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (M.op X1 X1) (M.op (M.op (σ x) (σ x)) X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3116 eq1123
    | exact resolve eq1123 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq87945 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq87516 x x
       have i₂ := eq383 sF2 x x
       grind)
    | exact superpose eq383 eq87516
    | exact resolve eq87516 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87516
  have eq87970 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq87945 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 sF2 x
       grind)
    | exact superpose eq14 eq87945
    | exact resolve eq87945 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87945
  have eq374972 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9045 X0 X1 X2
       have i₂ := eq1506 X0 X1 X2
       grind)
    | exact superpose eq1506 eq9045
    | (have j0 := eq9045 X0 X1 X2
       grind)
    | exact resolve eq9045 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506 eq9045
  have eq490739 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq8421 X0
       have j1 := eq374972 (M.op X0 X0) X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq8421 x
       have r₂ := eq374972 (M.op x x) x x
       grind)
    | exact resolve eq8421 eq374972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8421 eq374972
  have eq490850 : y = (k y (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq490739 (M.op y y)
       have i₂ := eq1254 y
       grind)
    | exact superpose eq1254 eq490739
    | exact resolve eq490739 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq491939 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq490850
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq490850
    | exact resolve eq490850 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981 eq490850
  have eq491975 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq491939
  have eq492107 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq491975
       grind)
    | exact superpose eq491975 eq69
    | exact resolve eq69 eq491975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq491975
  have eq492178 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq492107
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq492107
    | exact resolve eq492107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq492107
  have eq492283 : (σ y) = (M.op x (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq492178 eq49382
    | exact resolve eq49382 eq492178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49382
  have eq492287 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq492178 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq492178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq492178
  have eq492296 : (σ y) = (M.op x (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq492283
  have eq492308 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq492287
    | exact resolve eq492287 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492287
  have eq492309 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq492308
  have eq496542 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq492296
       have i₂ := eq1398 x sF3 x
       grind)
    | (have i₁ := eq492296
       have i₂ := eq1398 X0 sF3 x
       grind)
    | exact superpose eq1398 eq492296
    | exact resolve eq492296 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492296
  have eq502091 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq496542 eq1398
    | exact resolve eq1398 eq496542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502313 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq496542 eq3087
    | exact resolve eq3087 eq496542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087 eq496542
  have eq502856 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq502313 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502313
  have eq517683 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq502091
    | (have j0 := eq502091 X0 (σ x)
       grind)
    | exact resolve eq502091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502091
  have eq526456 : (σ y) = (M.op x (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq502856 eq492309
    | exact resolve eq492309 eq502856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492309 eq502856
  have eq527242 : (σ y) = (M.op x (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq526456
  have eq529769 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq527242 eq15551
    | exact resolve eq15551 eq527242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15551 eq527242
  have eq529905 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq529769
  have eq530017 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq529905 eq517683
    | exact resolve eq517683 eq529905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517683 eq529905
  have eq530102 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq530017
  have eq530870 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq530102 eq27
    | exact resolve eq27 eq530102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq530889 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (M.op X1 X1) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq530102 eq1123
    | exact resolve eq1123 eq530102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq530901 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq530102 eq3568
    | exact resolve eq3568 eq530102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq531000 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq204 eq530901
    | exact resolve eq530901 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq530901
  have eq531001 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq530889 x x
       have i₂ := eq383 sF2 x x
       grind)
    | exact superpose eq383 eq530889
    | exact resolve eq530889 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq530889
  have eq531005 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq530102 eq531000
    | exact resolve eq531000 eq530102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531000
  have eq533050 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq531005
       have i₂ := eq1398 sF2 sF2 x
       grind)
    | (have i₁ := eq531005
       have i₂ := eq1398 X0 sF2 sF2
       grind)
    | exact superpose eq1398 eq531005
    | exact resolve eq531005 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533076 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq531005 eq1444
    | exact resolve eq1444 eq531005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq533077 : x = (M.op (σ x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq531005 eq1445
    | exact resolve eq1445 eq531005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq531005
  have eq537904 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq533050 eq490739
    | exact resolve eq490739 eq533050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490739
  have eq551311 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq533050 eq533076
    | exact resolve eq533076 eq533050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533050
  have eq553081 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq551311
    | (have j0 := eq551311 (σ y)
       grind)
    | exact resolve eq551311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq551311
  have eq553351 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq530102 eq553081
    | exact resolve eq553081 eq530102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530102 eq553081
  have eq553428 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq553351 eq531001
    | exact resolve eq531001 eq553351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531001
  have eq553431 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq553351 eq537904
    | exact resolve eq537904 eq553351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537904 eq553351
  have eq556609 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq553431 eq116
    | exact resolve eq116 eq553431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq553431
  have eq556633 : y = (M.op y x) := by
    first
    | (have r₁ := eq556609
       have r₂ := eq530870
       grind)
    | exact resolve eq556609 eq530870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556609
  have eq557789 : y = (M.op (σ x) (M.op y y)) := by
    first
    | (have i₁ := eq533076 y x
       have i₂ := eq556633
       grind)
    | exact superpose eq556633 eq533076
    | exact resolve eq533076 eq556633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533076
  have eq564224 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq557789
       have i₂ := eq1398 sF2 y x
       grind)
    | (have i₁ := eq557789
       have i₂ := eq1398 X0 y sF2
       grind)
    | exact superpose eq1398 eq557789
    | exact resolve eq557789 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq564259 : (M.op (M.op x y) x) = (M.op y x) := by
    first
    | exact superpose eq557789 eq1451
    | exact resolve eq1451 eq557789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq557789
  have eq564397 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq564259
       have i₂ := eq556633
       grind)
    | exact superpose eq556633 eq564259
    | exact resolve eq564259 eq556633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556633 eq564259
  have eq564547 : x = (M.op (σ x) y) := by
    first
    | exact superpose eq564397 eq533077
    | exact resolve eq533077 eq564397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533077 eq564397
  have eq566582 : (M.op y y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq553428 (M.op y y)
       have i₂ := eq564224 sF3
       grind)
    | exact superpose eq564224 eq553428
    | exact resolve eq553428 eq564224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553428 eq564224
  have eq566617 : x = (M.op y y) := by
    first
    | exact superpose eq564547 eq566582
    | exact resolve eq566582 eq564547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566582
  have eq567294 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87970 y y
       have i₂ := eq566617
       grind)
    | exact superpose eq566617 eq87970
    | exact resolve eq87970 eq566617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87970 eq566617
  have eq567320 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq564547 eq567294
    | exact resolve eq567294 eq564547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564547 eq567294
  have eq567433 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq567320
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq567320
    | exact resolve eq567320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq567320
  have eq567434 : x = (M.op x y) := by grind
  clear eq567433
  have eq568211 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq567434 eq20
    | exact resolve eq20 eq567434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq567434
  have eq568748 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq568211
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq568211
    | exact resolve eq568211 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq568211
  have eq568799 : False := by grind
  exact eq568799

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq71
    | exact resolve eq71 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq87
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq87
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1549 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq486 X3 X1 x
       have i₂ := eq486 X0 X1 x
       grind)
    | (have i₁ := eq486 X0 X1 X3
       have i₂ := eq486 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq486 eq486
    | exact resolve eq486 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq13215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq13216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq13215
    | exact resolve eq13215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq13226 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13216
       have r₂ := eq28
       grind)
    | exact resolve eq13216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13216
  have eq13229 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq13226 eq113
    | exact resolve eq113 eq13226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq13226
  have eq13336 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq13229
    | exact resolve eq13229 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13229
  have eq13337 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13336
  have eq13340 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq13337
       grind)
    | exact superpose eq13337 eq88
    | exact resolve eq88 eq13337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13400 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1549 X0 y x
       have i₂ := eq13337
       grind)
    | exact superpose eq13337 eq1549
    | exact resolve eq1549 eq13337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13337
  have eq13456 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13340
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13340
    | exact resolve eq13340 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13340
  have eq13520 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13456 eq1549
    | exact resolve eq1549 eq13456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq13456
  have eq13909 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13400 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13400
    | (have j0 := eq13400 x X0
       grind)
    | exact resolve eq13400 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13400
  have eq14412 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq13909 y
       grind)
    | exact superpose eq13909 eq88
    | exact resolve eq88 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq13909
  have eq14437 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq14412
    | exact resolve eq14412 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14412
  have eq30893 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq13520
    | (have j0 := eq13520 (σ x) X0
       grind)
    | exact resolve eq13520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13520
  have eq31460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30893 eq14437
    | exact resolve eq14437 eq30893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437 eq30893
  have eq31471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31460
  have eq31489 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq31471
       have r₂ := eq28
       grind)
    | exact resolve eq31471 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31471
  have eq31494 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31489 eq30
    | exact resolve eq30 eq31489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31489
  have eq31681 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq31494
    | exact resolve eq31494 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31494
  have eq31682 : x = y := by grind
  clear eq31681
  have eq31695 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq31682
       grind)
    | exact superpose eq31682 eq19
    | exact resolve eq19 eq31682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31696 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq31682
       grind)
    | exact superpose eq31682 eq25
    | exact resolve eq25 eq31682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31682
  have eq31817 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31696
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31696
    | exact resolve eq31696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31696
  have eq31837 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31817 eq27
    | exact resolve eq27 eq31817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq31817
  have eq32168 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31837 eq78
    | exact resolve eq78 eq31837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq31837
  have eq32266 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32168
       have i₂ := eq31695
       grind)
    | exact superpose eq31695 eq32168
    | exact resolve eq32168 eq31695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31695 eq32168
  have eq32274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32266 eq15
    | exact resolve eq15 eq32266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32266
  have eq32350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32274
    | exact resolve eq32274 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32274
  have eq32371 : False := by grind
  exact eq32371

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq71
    | exact resolve eq71 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq87
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq87
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1549 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq486 X3 X1 x
       have i₂ := eq486 X0 X1 x
       grind)
    | (have i₁ := eq486 X0 X1 X3
       have i₂ := eq486 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq486 eq486
    | exact resolve eq486 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq13219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq13220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq13219
    | exact resolve eq13219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13219
  have eq13230 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13220
       have r₂ := eq28
       grind)
    | exact resolve eq13220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13220
  have eq13233 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq13230 eq113
    | exact resolve eq113 eq13230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq13230
  have eq13340 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq13233
    | exact resolve eq13233 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13233
  have eq13341 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13340
  have eq13345 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq13341
       grind)
    | exact superpose eq13341 eq88
    | exact resolve eq88 eq13341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13405 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1549 X0 y x
       have i₂ := eq13341
       grind)
    | exact superpose eq13341 eq1549
    | exact resolve eq1549 eq13341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13341
  have eq13461 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13345
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13345
    | exact resolve eq13345 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13345
  have eq13822 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13461 eq1549
    | exact resolve eq1549 eq13461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq13461
  have eq14758 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13405 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13405
    | (have j0 := eq13405 x X0
       grind)
    | exact resolve eq13405 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13405
  have eq15140 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq14758 y
       grind)
    | exact superpose eq14758 eq88
    | exact resolve eq88 eq14758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq14758
  have eq15165 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq15140
    | exact resolve eq15140 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140
  have eq39971 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq13822
    | (have j0 := eq13822 (σ x) X0
       grind)
    | exact resolve eq13822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13822
  have eq40569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39971 eq15165
    | exact resolve eq15165 eq39971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165 eq39971
  have eq40580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40569
  have eq40598 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40580
       have r₂ := eq28
       grind)
    | exact resolve eq40580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40580
  have eq40935 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq40598 eq30
    | exact resolve eq30 eq40598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40598
  have eq41142 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq40935
    | exact resolve eq40935 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40935
  have eq41143 : x = y := by grind
  clear eq41142
  have eq41160 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq41143
       grind)
    | exact superpose eq41143 eq19
    | exact resolve eq19 eq41143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq41161 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq41143
       grind)
    | exact superpose eq41143 eq25
    | exact resolve eq25 eq41143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq41143
  have eq41282 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41161
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq41161
    | exact resolve eq41161 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq41161
  have eq41302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41282 eq27
    | exact resolve eq27 eq41282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq41282
  have eq42106 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41302 eq78
    | exact resolve eq78 eq41302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq41302
  have eq42221 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq42106
       have i₂ := eq41160
       grind)
    | exact superpose eq41160 eq42106
    | exact resolve eq42106 eq41160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41160 eq42106
  have eq42225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42221 eq15
    | exact resolve eq15 eq42221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42221
  have eq42301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq42225
    | exact resolve eq42225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42225
  have eq42322 : False := by grind
  exact eq42322

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq532 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210
    | exact resolve eq210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq16
    | (have j1 := eq210 x y
       grind)
    | exact resolve eq16 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq559 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq532
  have eq565 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq559
    | exact resolve eq559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq636 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq565 (τ X0) X1
       grind)
    | exact superpose eq565 eq18
    | (have j1 := eq565 (τ X0) X1
       grind)
    | exact resolve eq18 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq565
  have eq851 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq636
    | exact resolve eq636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq902 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq987 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq540
       have i₂ := eq902 x y
       grind)
    | exact superpose eq902 eq540
    | (have j1 := eq902 (σ x) (σ y)
       grind)
    | (have r₁ := eq540
       have r₂ := eq902 x y
       grind)
    | exact resolve eq540 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq987
  have eq1029 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq988
  have eq1039 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq540
       have i₂ := eq1029
       grind)
    | exact superpose eq1029 eq540
    | exact resolve eq540 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1029
  have eq1040 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1039
  have eq1041 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1040
  have eq1089 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1041
  have eq1101 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1089
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1089
    | exact resolve eq1089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1106 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1101
       grind)
    | exact superpose eq1101 eq16
    | exact resolve eq16 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq902 x y
       grind)
    | exact superpose eq902 eq1106
    | (have j1 := eq902 x y
       grind)
    | (have r₁ := eq1106
       have r₂ := eq902 x y
       grind)
    | exact resolve eq1106 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq1145 : x = (M.op y y) := by grind
  clear eq1144
  have eq1150 : (M.op x y) = (k x y) := by grind
  clear eq1145
  have eq1203 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq1150
       grind)
    | exact superpose eq1150 eq1106
    | exact resolve eq1106 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq1150
  have eq1206 : False := by grind
  exact eq1206

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq182 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq213 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq182
    | (have j0 := eq182 X0 X1
       grind)
    | exact resolve eq182 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq182
  have eq218 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq213 X0 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq213 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq213
  have eq222 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq218
    | (have j0 := eq218 X0 X1
       grind)
    | exact resolve eq218 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq486 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq222
    | exact resolve eq222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq541 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0
       have i₂ := eq486 X1 (τ X0)
       grind)
    | (have i₁ := eq68 X0
       have i₂ := eq486 (τ X0) (τ X0)
       grind)
    | exact superpose eq486 eq68
    | (have j1 := eq486 X1 (τ X0)
       grind)
    | exact resolve eq68 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq544 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq486 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq486 X0 X1
       grind)
    | exact superpose eq486 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq486 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq486 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq486 X0 X1
       grind)
    | exact resolve eq13 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq486 (σ y) (σ x)
       grind)
    | exact superpose eq486 eq16
    | (have j1 := eq486 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq555 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq561 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq549
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq549
    | exact resolve eq549 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq564 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq555 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq555 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq555 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq570 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq571 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq564
    | exact resolve eq564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq564 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq610 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq571
    | (have j0 := eq571 X0 X1
       grind)
    | exact resolve eq571 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq1836 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq541
    | exact resolve eq541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1859 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1836 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1836
    | (have j0 := eq1836 X0 X1
       grind)
    | exact resolve eq1836 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1836
  have eq4174 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq610 x y
       grind)
    | exact superpose eq610 eq16
    | (have j1 := eq610 x y
       grind)
    | exact resolve eq16 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq4355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4174
       have i₂ := eq1859 x y
       grind)
    | exact superpose eq1859 eq4174
    | (have j1 := eq1859 x y
       grind)
    | exact resolve eq4174 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859 eq4174
  have eq4362 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq4355
  have eq4363 : (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq4362
  have eq4539 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq570
       have i₂ := eq4363
       grind)
    | exact superpose eq4363 eq570
    | (have r₁ := eq570
       have r₂ := eq4363
       grind)
    | exact resolve eq570 eq4363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq4540 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq4363
       grind)
    | exact superpose eq4363 eq10
    | exact resolve eq10 eq4363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4579 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq4539
  have eq4597 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4540
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq4540
    | exact resolve eq4540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4540
  have eq4608 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq595 x y
       have i₂ := eq4597
       grind)
    | exact superpose eq4597 eq595
    | (have j0 := eq595 x x
       grind)
    | (have r₁ := eq595 x y
       have r₂ := eq4597
       grind)
    | exact resolve eq595 eq4597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq4597
  have eq4609 : (k x y) = (M.op x x) := by grind
  clear eq4608
  have eq4813 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4579
       grind)
    | exact superpose eq4579 eq16
    | exact resolve eq16 eq4579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4579
  have eq4845 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4813
       have i₂ := eq4609
       grind)
    | exact superpose eq4609 eq4813
    | exact resolve eq4813 eq4609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4609 eq4813
  have eq4856 : False := by grind
  exact eq4856

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq347 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq499 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq347 X1 (σ X0)
       grind)
    | exact superpose eq347 eq15
    | (have j1 := eq347 X1 (σ X0)
       grind)
    | exact resolve eq15 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq550 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq499 X1 (τ X0)
       grind)
    | exact superpose eq499 eq17
    | (have j1 := eq499 X1 (τ X0)
       grind)
    | exact resolve eq17 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq499
  have eq665 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq550
    | exact resolve eq550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq550 X1 X0
       grind)
    | exact superpose eq550 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq550 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq550 X0 X1
       grind)
    | exact resolve eq13 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq700 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq723 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq1005 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq510 x y
       grind)
    | exact superpose eq510 eq16
    | (have j1 := eq510 x y
       grind)
    | exact resolve eq16 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1029 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq510 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq11342 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq700 X1 X0
       grind)
    | exact superpose eq700 eq10
    | (have j1 := eq700 X1 X0
       grind)
    | exact resolve eq10 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq11394 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11342 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq11342
    | (have j0 := eq11342 X0 X1
       grind)
    | exact resolve eq11342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11342
  have eq11417 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11394 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq11394 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11394 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11394
  have eq11445 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11417 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11417
    | exact resolve eq11417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11417
  have eq11743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq11445 x y
       grind)
    | exact superpose eq11445 eq1005
    | (have j1 := eq11445 x y
       grind)
    | exact resolve eq1005 eq11445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq11744 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11445
  have eq11745 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11743
  have eq11900 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1029 x y
       have i₂ := eq11745
       grind)
    | exact superpose eq11745 eq1029
    | (have j0 := eq1029 x y
       grind)
    | exact resolve eq1029 eq11745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq11745
  have eq11920 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11900
  have eq11921 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11920
  have eq11928 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11921
       grind)
    | exact superpose eq11921 eq16
    | exact resolve eq16 eq11921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11935 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11744 (σ x) (σ y)
       have i₂ := eq11921
       grind)
    | exact superpose eq11921 eq11744
    | (have j0 := eq11744 (σ x) (σ y)
       grind)
    | (have r₁ := eq11744 (σ x) (σ y)
       have r₂ := eq11921
       grind)
    | exact resolve eq11744 eq11921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11744 eq11921
  have eq11936 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq11935
  have eq11938 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq11936
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq11936
    | exact resolve eq11936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11936
  have eq11973 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq723 x y
       have i₂ := eq11938
       grind)
    | exact superpose eq11938 eq723
    | (have j0 := eq723 x y
       grind)
    | exact resolve eq723 eq11938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq11938
  have eq12044 : y = (M.op x y) := by
    first
    | (have r₁ := eq11973
       have r₂ := eq11928
       grind)
    | exact resolve eq11973 eq11928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11973
  have eq12087 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq11928
       have i₂ := eq12044
       grind)
    | exact superpose eq12044 eq11928
    | exact resolve eq11928 eq12044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11928 eq12044
  have eq12100 : False := by grind
  exact eq12100

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1728 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq530 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
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
  have eq560 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq563 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq586 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq3670 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq560
    | exact resolve eq560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq3716 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3670 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3670
    | (have j0 := eq3670 X0 X1
       grind)
    | exact resolve eq3670 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3757 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq586 x y
       grind)
    | exact superpose eq586 eq16
    | (have j1 := eq586 x y
       grind)
    | exact resolve eq16 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3767 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq7457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3757
       have i₂ := eq3716 y x
       grind)
    | exact superpose eq3716 eq3757
    | (have j1 := eq3716 y x
       grind)
    | (have r₁ := eq3757
       have r₂ := eq3716 y x
       grind)
    | (have r₁ := eq3757
       have r₂ := eq3716 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3757
       have r₂ := eq3716 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3757 eq3716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716 eq3757
  have eq7458 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7457
  have eq7470 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3767 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3767
    | (have j0 := eq3767 (τ X0) (τ X1)
       grind)
    | exact resolve eq3767 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7537 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7470 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7470
    | (have j0 := eq7470 X0 X1
       grind)
    | exact resolve eq7470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7470
  have eq7572 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7537 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7537
    | (have j0 := eq7537 X0 X1
       grind)
    | exact resolve eq7537 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537
  have eq7604 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7572 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7572
    | (have j0 := eq7572 X0 X1
       grind)
    | exact resolve eq7572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7572
  have eq7630 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7604 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7604
    | (have j0 := eq7604 X0 X1
       grind)
    | exact resolve eq7604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7604
  have eq7649 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7630 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7630
    | (have j0 := eq7630 X0 X1
       grind)
    | exact resolve eq7630 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7630
  have eq7666 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7649 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7649
    | (have j0 := eq7649 X0 X1
       grind)
    | exact resolve eq7649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7649
  have eq7679 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7666
    | (have j0 := eq7666 X0 X1
       grind)
    | exact resolve eq7666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7666
  have eq15559 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7458
       grind)
    | exact superpose eq7458 eq16
    | exact resolve eq16 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458
  have eq15560 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15559
       have r₂ := eq22 x
       grind)
    | exact resolve eq15559 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15559
  have eq15562 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15560
       grind)
    | exact superpose eq15560 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15560
       grind)
    | exact resolve eq13 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15560
  have eq15564 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15562
  have eq17487 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15564
       grind)
    | exact superpose eq15564 eq16
    | exact resolve eq16 eq15564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15564
  have eq17488 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq17487
       have r₂ := eq22 x
       grind)
    | exact resolve eq17487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17487
  have eq17492 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq530 x (σ y)
       have i₂ := eq17488
       grind)
    | exact superpose eq17488 eq530
    | (have j0 := eq530 x (σ y)
       grind)
    | (have r₁ := eq530 x (σ y)
       have r₂ := eq17488
       grind)
    | exact resolve eq530 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17488
  have eq17505 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq17492
  have eq17506 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq17505
  have eq17512 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17506
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17506
    | exact resolve eq17506 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17506
  have eq17525 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3767 x y
       have i₂ := eq17512
       grind)
    | exact superpose eq17512 eq3767
    | (have j0 := eq3767 x y
       grind)
    | (have r₁ := eq3767 x y
       have r₂ := eq17512
       grind)
    | exact resolve eq3767 eq17512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512
  have eq17550 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq17525
  have eq17551 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq17550
  have eq17555 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3767 x y
       grind)
    | (have r₁ := eq17551
       have r₂ := eq3767 x y
       grind)
    | exact resolve eq17551 eq3767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767 eq17551
  have eq17558 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17555
       grind)
    | exact superpose eq17555 eq16
    | exact resolve eq16 eq17555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17560 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq530 x (σ y)
       have i₂ := eq17555
       grind)
    | exact superpose eq17555 eq530
    | (have j0 := eq530 x (σ y)
       grind)
    | (have r₁ := eq530 x (σ y)
       have r₂ := eq17555
       grind)
    | exact resolve eq530 eq17555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq17555
  have eq17573 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq17560
  have eq17574 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq17573
  have eq17580 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17574
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17574
    | exact resolve eq17574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17574
  have eq17590 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17580
       grind)
    | exact superpose eq17580 eq10
    | exact resolve eq10 eq17580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17580
  have eq17755 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17590
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17590
    | exact resolve eq17590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17590
  have eq17757 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17755
       grind)
    | exact superpose eq17755 eq16
    | exact resolve eq16 eq17755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17755
  have eq17758 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17757
       have r₂ := eq22 x
       grind)
    | exact resolve eq17757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17757
  have eq17771 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq17758
       grind)
    | exact superpose eq17758 eq10
    | exact resolve eq10 eq17758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17758
  have eq17937 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq17771
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17771
    | exact resolve eq17771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17771
  have eq17966 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7679 x y
       have i₂ := eq17937
       grind)
    | exact superpose eq17937 eq7679
    | (have j0 := eq7679 x y
       grind)
    | (have r₁ := eq7679 x y
       have r₂ := eq17937
       grind)
    | exact resolve eq7679 eq17937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7679 eq17937
  have eq17969 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17966
  have eq17973 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17558
       have i₂ := eq17969
       grind)
    | exact superpose eq17969 eq17558
    | exact resolve eq17558 eq17969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17558 eq17969
  have eq17982 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17973
  have eq17983 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17982
       grind)
    | exact superpose eq17982 eq16
    | exact resolve eq16 eq17982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17982
  have eq17986 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17983
       have r₂ := eq22 x
       grind)
    | exact resolve eq17983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17983
  have eq17987 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17986
       grind)
    | exact superpose eq17986 eq16
    | exact resolve eq16 eq17986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17988 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17986
       grind)
    | exact superpose eq17986 eq10
    | exact resolve eq10 eq17986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17986
  have eq18153 : x = y := by
    first
    | (have i₁ := eq17988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17988
    | exact resolve eq17988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17988
  have eq18154 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17987
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17987
    | exact resolve eq17987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17987
  have eq18155 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18154
       have i₂ := eq18153
       grind)
    | exact superpose eq18153 eq18154
    | exact resolve eq18154 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18153 eq18154
  have eq18156 : False := by grind
  exact eq18156

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation177 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq49 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq53 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq60 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq60
    | (have j0 := eq60 y
       grind)
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq151 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ x) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39 eq28
    | exact resolve eq28 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
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
  have eq157 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq28 X1 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k X0 X1)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq158 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq158 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq186 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq156
       grind)
    | exact superpose eq156 eq53
    | exact resolve eq53 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq186
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq186
    | exact resolve eq186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq189 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq187
    | exact resolve eq187 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq189 eq157
    | exact resolve eq157 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq193
       have r₂ := eq27
       grind)
    | exact resolve eq193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq198 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq196 eq40
    | exact resolve eq40 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq196 eq39
    | exact resolve eq39 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq198
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq198
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq206 eq16
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op (σ x) (σ x)) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq221 eq16
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq231 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq227 eq16
    | exact resolve eq16 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq237 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq231 eq35
    | exact resolve eq35 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq287 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq289 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ≠ (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ x) = (k (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq237 eq12
    | (have j0 := eq12 (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))
       have r₂ := eq237
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq237
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq237
       grind)
    | exact resolve eq12 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq290 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ x) = (k (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq289
  have eq294 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (k (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq290
       have i₂ := eq16 (k sF3 sF3) (k sF3 sF3)
       grind)
    | exact superpose eq16 eq290
    | exact resolve eq290 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq300 : (σ x) = (k (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq294
    | (have j1 := eq28 (k (σ y) (σ y)) (k (σ y) (σ y))
       grind)
    | exact resolve eq294 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq329 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq518 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq15
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq543 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq175
    | (have j0 := eq175 (σ X0) (σ X1)
       grind)
    | exact resolve eq175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq184 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq184
    | (have j0 := eq184 (σ X0) X1
       grind)
    | exact resolve eq184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq36
    | exact resolve eq36 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198 eq36
    | exact resolve eq36 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq845 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0))
       have i₂ := eq36 (M.op X1 X1) X0
       grind)
    | exact superpose eq36 eq35
    | exact resolve eq35 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq818
       have i₂ := eq845 sF3 (M.op sF3 sF3)
       grind)
    | exact superpose eq845 eq818
    | exact resolve eq818 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq877 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq862
       have i₂ := eq846 sF3 sF3
       grind)
    | exact superpose eq846 eq862
    | exact resolve eq862 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq862
  have eq891 : (M.op (σ x) (σ x)) = (M.op (σ y) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq877
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq877
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq877 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq877 eq35
    | exact resolve eq35 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : (σ y) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq891 eq16
    | exact resolve eq16 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq941 : (σ y) = (M.op (M.op (k (σ y) (σ y)) (σ x)) (M.op (k (σ y) (σ y)) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq940
       have i₂ := eq845 sF2 (k sF3 sF3)
       grind)
    | exact superpose eq845 eq940
    | exact resolve eq940 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq940
  have eq943 : (σ y) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq206 eq941
    | exact resolve eq941 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq941
  have eq976 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq943 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq175 x y
       grind)
    | (have r₁ := eq976
       have r₂ := eq175 (σ y) (σ y)
       grind)
    | exact resolve eq976 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1034 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq999 eq300
    | exact resolve eq300 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq999
  have eq1063 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1034
  have eq1077 : (σ (M.op x y)) = (σ x) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq189 eq1063
    | exact resolve eq1063 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1084 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq943 eq1077
    | exact resolve eq1077 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq1077
  have eq1086 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq175 (σ y) (σ y)
       grind)
    | (have r₁ := eq1084
       have r₂ := eq175 (σ y) (σ y)
       grind)
    | exact resolve eq1084 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1096 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1086 eq877
    | exact resolve eq877 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1086 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1086
       grind)
    | exact resolve eq13 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1086 eq36
    | exact resolve eq36 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1103 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1105 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1096
  have eq1113 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq199 eq1101
    | exact resolve eq1101 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1101
  have eq1114 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1103 eq1105
    | exact resolve eq1105 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq1105
  have eq1116 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1113 eq1114
    | exact resolve eq1114 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1126 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1113 eq189
    | exact resolve eq189 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1197 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1113 eq877
    | exact resolve eq877 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq1199 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1113 eq893
    | exact resolve eq893 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq1113
  have eq1216 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1199
  have eq1218 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1197
  have eq1291 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1126
  have eq1292 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1116 eq1216
    | exact resolve eq1216 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1293 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1116 eq1218
    | exact resolve eq1218 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq1218
  have eq1308 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1291 eq1292
    | exact resolve eq1292 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1309 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1291 eq1293
    | exact resolve eq1293 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq1293
  have eq1318 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1308 eq1309
    | exact resolve eq1309 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq1309
  have eq1319 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1318
  have eq1329 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1319 eq29
    | exact resolve eq29 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1319
  have eq1331 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1329
    | exact resolve eq1329 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1338 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq18
    | exact resolve eq18 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq24
    | exact resolve eq24 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq37
    | exact resolve eq37 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1343 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq287
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq287
    | (have r₁ := eq287
       have r₂ := eq1331
       grind)
    | exact resolve eq287 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq1331
  have eq1344 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1343
  have eq1347 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1339
    | exact resolve eq1339 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1382 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1340 eq28
    | exact resolve eq28 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1382
  have eq1388 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1384 eq54
    | exact resolve eq54 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1390 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1388
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1388
    | exact resolve eq1388 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1391 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1347 eq1390
    | exact resolve eq1390 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1546 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq151
    | exact resolve eq151 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1597 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1546 X0 X1
       have i₂ := eq802 X0 X1
       grind)
    | exact superpose eq802 eq1546
    | (have j0 := eq1546 (k (M.op (M.op X0 X0) X1) X0) X1
       grind)
    | exact resolve eq1546 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq1546
  have eq1629 : (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1391
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq1391
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1391 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1632 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq54 eq1629
    | exact resolve eq1629 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq1633 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq1632
    | exact resolve eq1632 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1634 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1347 eq1633
    | exact resolve eq1633 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1820 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1344 eq1340
    | exact resolve eq1340 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1829 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq1820
  have eq1835 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1344 eq1829
    | exact resolve eq1829 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344 eq1829
  have eq1836 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1835
  have eq1841 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1836 eq54
    | exact resolve eq54 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1843 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1841
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1841
    | exact resolve eq1841 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1845 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1347 eq1843
    | exact resolve eq1843 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1845 eq157
    | exact resolve eq157 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1861 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1852 eq27
    | exact resolve eq27 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq1864 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1861
       have r₂ := eq1347
       grind)
    | exact resolve eq1861 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1867 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1864 eq27
    | exact resolve eq27 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1868 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1864 eq39
    | exact resolve eq39 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1874 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1347 eq1867
    | exact resolve eq1867 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347 eq1867
  have eq1877 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1874
  have eq2139 : ∀ X0 X1 : G, (M.op (k X1 X1) (k X0 X1)) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq160
    | (have j0 := eq160 X1 X1
       have j1 := eq28 X1 X1
       grind)
    | exact resolve eq160 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq2308 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X1) (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq161
    | (have j0 := eq161 (σ X0) (σ X1)
       grind)
    | exact resolve eq161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : (M.op (M.op (σ y) (σ y)) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1391 eq161
    | (have j0 := eq161 (σ (M.op (M.op x y) (M.op x y))) (σ y)
       grind)
    | exact resolve eq161 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2385 : (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1868 eq2309
    | exact resolve eq2309 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868 eq2309
  have eq2654 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2385 eq12
    | (have j0 := eq12 (σ (M.op (M.op x y) (M.op x y))) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op (M.op x y) (M.op x y))) (σ y)
       have r₂ := eq2385
       grind)
    | exact resolve eq12 eq2385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq2656 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2654
  have eq2659 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1391 eq2656
    | exact resolve eq2656 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391 eq2656
  have eq2660 : (σ x) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2659
  have eq2675 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2660 eq15
    | exact resolve eq15 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660
  have eq2689 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2675
    | exact resolve eq2675 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675
  have eq2717 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2689 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq2689
       grind)
    | exact resolve eq13 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2722 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq2840 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2722 eq2689
    | exact resolve eq2689 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689 eq2722
  have eq2841 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2840
  have eq2951 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2841 eq1634
    | exact resolve eq1634 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq2960 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq2951
  have eq2988 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2841 eq2960
    | exact resolve eq2960 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841 eq2960
  have eq2992 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq2988
       have r₂ := eq1877
       grind)
    | exact resolve eq2988 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877 eq2988
  have eq2998 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2992 eq1340
    | exact resolve eq1340 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3024 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2998
  have eq3040 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3024 eq1340
    | exact resolve eq1340 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq3024
  have eq3071 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3040
  have eq3078 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1338 eq3071
    | exact resolve eq3071 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338 eq3071
  have eq3079 : x = (M.op x y) := by grind
  clear eq3078
  have eq3081 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq18
    | exact resolve eq18 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3082 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq22
    | exact resolve eq22 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3083 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq38
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq38
    | exact resolve eq38 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq3085 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq52
    | exact resolve eq52 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3086 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq156
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq156
    | exact resolve eq156 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq3090 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3082 eq20
    | exact resolve eq20 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3312 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3319 : ∀ X0 : G, (k (k X0 y) x) = (τ (k (k (σ X0) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq72 (k X0 y)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq72
    | exact resolve eq72 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3330 : ∀ X0 : G, (τ (k (k (σ X0) (σ y)) (σ x))) = (k (k X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3319 X0
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq3319
    | exact resolve eq3319 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3337 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq3312 X0
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq3312
    | exact resolve eq3312 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312
  have eq3370 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq3081 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3371 : (M.op x y) = (M.op (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq3081 eq16
    | exact resolve eq16 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3377 : y = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq3370
       have r₂ := eq3086
       grind)
    | exact resolve eq3370 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq3379 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3086 eq3377
    | exact resolve eq3377 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086 eq3377
  have eq3390 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op y y)) := by
    first
    | exact superpose eq3371 eq36
    | exact resolve eq36 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3728 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3379 eq53
    | exact resolve eq53 eq3379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379
  have eq3732 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq3728
    | exact resolve eq3728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq3736 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3090 eq3732
    | exact resolve eq3732 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3746 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3736 eq157
    | exact resolve eq157 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq3761 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3390
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq3390
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq3390 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3806 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3746 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq3746
       grind)
    | exact resolve eq13 eq3746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3813 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3806 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3893 : ∀ X0 : G, (k (k (τ X0) y) (M.op x y)) = (τ (k (k X0 (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq3330 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq3330
    | exact resolve eq3330 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330
  have eq3930 : ∀ X0 : G, (k (k (τ X0) y) (M.op x y)) = (k (τ (k X0 (σ y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3337 eq3893
    | exact resolve eq3893 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq4095 : (k (k (τ (σ x)) y) (M.op x y)) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157 eq3930
    | exact resolve eq3930 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930
  have eq4111 : (k (k x y) (M.op x y)) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq4095
    | exact resolve eq4095 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq4124 : (k (k (M.op x y) y) (M.op x y)) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4111
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq4111
    | exact resolve eq4111 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq4136 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq196 eq4124
    | exact resolve eq4124 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4153 : (k (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))) = (σ (k (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4136 eq54
    | exact resolve eq54 eq4136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4156 : (k (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))) = (k (σ (τ (M.op (σ x) (σ y)))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54 eq4153
    | exact resolve eq4153 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153
  have eq4158 : (k (σ (k (M.op x y) (M.op x y))) (σ x)) = (k (σ (τ (M.op (σ x) (σ y)))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq4156
    | exact resolve eq4156 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156
  have eq4160 : (k (σ (k (M.op x y) (M.op x y))) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4158
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq4158
    | exact resolve eq4158 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq4162 : (k (M.op (σ x) (σ y)) (σ x)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54 eq4160
    | exact resolve eq4160 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4160
  have eq4164 : (k (k (σ (M.op x y)) (σ x)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq4162
    | exact resolve eq4162 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162
  have eq4166 : (k (k (σ (M.op x y)) (σ x)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4164
    | exact resolve eq4164 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4164
  have eq4168 : (k (k (σ x) (σ x)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq4166
    | exact resolve eq4166 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq4427 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3813 eq3746
    | exact resolve eq3746 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746 eq3813
  have eq4429 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4427
  have eq4498 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4429 eq3085
    | exact resolve eq3085 eq4429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4429
  have eq4512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4498
    | exact resolve eq4498 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498
  have eq4517 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq4512
    | exact resolve eq4512 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512
  have eq4549 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4517 eq4168
    | exact resolve eq4168 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4554 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4517 eq175
    | (have j0 := eq175 (σ x) (σ x)
       grind)
    | (have r₁ := eq175 (σ x) (σ x)
       have r₂ := eq4517
       grind)
    | exact resolve eq175 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4555 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4554
  have eq4557 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4549
  have eq4566 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4517 eq4557
    | exact resolve eq4557 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4617 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4566 eq175
    | (have j0 := eq175 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq175 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq4566
       grind)
    | exact resolve eq175 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq4618 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4617
  have eq4625 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4618 eq151
    | (have j0 := eq151 (σ x) (σ y)
       grind)
    | exact resolve eq151 eq4618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4618
  have eq4628 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4625
  have eq4630 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4555 eq4628
    | exact resolve eq4628 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4555 eq4628
  have eq4633 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4517 eq4630
    | exact resolve eq4630 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517 eq4630
  have eq4634 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4633
  have eq6711 : ∀ X0 X1 : G, (k (τ X1) (k X0 (M.op x y))) = (τ (k X1 (k (σ X0) (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq3085 eq329
    | exact resolve eq329 eq3085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq6777 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq3082 eq518
    | exact resolve eq518 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq3082
  have eq6831 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157 eq6777
    | exact resolve eq6777 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq6777
  have eq6881 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq6831
    | exact resolve eq6831 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6831
  have eq6897 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq196 eq6881
    | exact resolve eq6881 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq6881
  have eq6906 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4634 eq6897
    | exact resolve eq6897 eq4634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6897
  have eq6908 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq6906
    | exact resolve eq6906 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq6910 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6908
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq6908
    | exact resolve eq6908 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6908
  have eq6928 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6910 eq3085
    | exact resolve eq3085 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6931 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6910 eq184
    | (have j0 := eq184 (M.op x y) X0
       grind)
    | (have r₁ := eq184 (M.op x y) x
       have r₂ := eq6910
       grind)
    | exact resolve eq184 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6933 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6910 eq175
    | (have j0 := eq175 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq175 (M.op x y) (M.op x y)
       have r₂ := eq6910
       grind)
    | exact resolve eq175 eq6910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6910
  have eq6934 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6933
  have eq6935 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931
  have eq6943 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6928
    | exact resolve eq6928 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6928
  have eq6950 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq6943
    | exact resolve eq6943 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6943
  have eq6986 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6934 eq16
    | exact resolve eq16 eq6934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6934
  have eq7001 : ∀ X0 : G, (M.op (M.op x y) (k X0 (M.op x y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6935 eq6986
    | exact resolve eq6986 eq6935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6986
  have eq7050 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6950 eq184
    | (have j0 := eq184 (σ x) X0
       grind)
    | (have r₁ := eq184 (σ x) x
       have r₂ := eq6950
       grind)
    | exact resolve eq184 eq6950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq7052 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6950 eq175
    | (have j0 := eq175 (σ x) (σ x)
       grind)
    | (have r₁ := eq175 (σ x) (σ x)
       have r₂ := eq6950
       grind)
    | exact resolve eq175 eq6950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq7053 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7052
  have eq7054 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7050
  have eq7106 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7053 eq16
    | exact resolve eq16 eq7053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7116 : ∀ X0 : G, (M.op (σ x) (k X0 (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7054 eq7106
    | exact resolve eq7106 eq7054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7106
  have eq7155 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6935 eq36
    | exact resolve eq36 eq6935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7252 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7001 eq36
    | exact resolve eq36 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001
  have eq7260 : ∀ X0 : G, (M.op (k X0 (M.op x y)) (k X0 (M.op x y))) = (k (M.op X0 X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6935 eq7252
    | exact resolve eq7252 eq6935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6935 eq7252
  have eq7307 : (M.op (σ y) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7054 eq40
    | exact resolve eq40 eq7054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7054
  have eq7351 : (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4634 eq7307
    | exact resolve eq7307 eq4634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4634 eq7307
  have eq7361 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7053 eq7351
    | exact resolve eq7351 eq7053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053 eq7351
  have eq7366 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6950 eq7361
    | exact resolve eq7361 eq6950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361
  have eq7410 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7366 eq151
    | exact resolve eq151 eq7366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq7366
  have eq7415 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6950 eq7410
    | exact resolve eq7410 eq6950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6950 eq7410
  have eq7416 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7415
  have eq7430 : (σ x) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7416 eq155
    | exact resolve eq155 eq7416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq7416
  have eq7435 : (σ x) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7430
  have eq7558 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7435
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq7435
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq7435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7435
  have eq8933 : ∀ X0 X1 : G, (τ (k X1 (k X0 (σ x)))) = (k (τ X1) (k (τ X0) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq6711 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq6711
    | exact resolve eq6711 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6711
  have eq9453 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) (k X0 (σ x)))) = (k (k y y) (k (τ X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq128 eq8933
    | exact resolve eq8933 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq8933
  have eq10022 : ∀ X0 : G, (τ X0) = (k (τ (M.op (M.op (σ x) (σ x)) X0)) (M.op x y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3337 (M.op (M.op sF2 sF2) x)
       have i₂ := eq1597 sF2 x
       grind)
    | exact superpose eq1597 eq3337
    | (have j1 := eq1597 (τ X0) (k (τ (M.op (M.op (σ x) (σ x)) X0)) (M.op x y))
       grind)
    | exact resolve eq3337 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq16592 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7155 eq7260
    | exact resolve eq7260 eq7155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7155 eq7260
  have eq16677 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0))) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16592
  have eq16695 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op x y) X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16677 X0
       have i₂ := eq16 (M.op sF0 X0) (M.op sF0 X0)
       grind)
    | exact superpose eq16 eq16677
    | exact resolve eq16677 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16677
  have eq16704 : ∀ X0 : G, (k (M.op (M.op x y) X0) (M.op x y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16695 X0
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq16695
    | exact resolve eq16695 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16695
  have eq16750 : ∀ X0 : G, (σ X0) = (k (σ (M.op (M.op x y) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16704 eq3085
    | exact resolve eq3085 eq16704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085 eq16704
  have eq16840 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ x) (σ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16750 eq7116
    | exact resolve eq7116 eq16750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7116 eq16750
  have eq16851 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ x) (σ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16840 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16840
  have eq16945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3081 eq16851
    | exact resolve eq16851 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16851
  have eq17081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16945
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16945
    | exact resolve eq16945 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16945
  have eq17114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17081
    | exact resolve eq17081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17081
  have eq17133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17114
    | exact resolve eq17114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17114
  have eq17148 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17133
       have r₂ := eq27
       grind)
    | exact resolve eq17133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17133
  have eq17157 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq17148 eq27
    | exact resolve eq27 eq17148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq17158 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq17148 eq39
    | exact resolve eq39 eq17148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq17159 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq17148 eq40
    | exact resolve eq40 eq17148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17148
  have eq17166 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq3090 eq17157
    | exact resolve eq17157 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17157
  have eq34728 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (k (k y y) (k (τ (M.op (M.op (σ x) (σ x)) X0)) (M.op x y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9453 (M.op (M.op sF2 sF2) x)
       have i₂ := eq1597 sF2 x
       grind)
    | exact superpose eq1597 eq9453
    | (have j1 := eq1597 (τ (k (k (σ y) (σ y)) X0)) (k (k y y) (k (τ (M.op (M.op (σ x) (σ x)) X0)) (M.op x y)))
       grind)
    | exact resolve eq9453 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597 eq9453
  have eq34857 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (k (k y y) (τ X0)) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq10022 eq34728
    | (have j0 := eq34728 X0
       have j1 := eq10022 X0
       grind)
    | exact resolve eq34728 eq10022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10022 eq34728
  have eq34978 : (τ (σ x)) = (k (k y y) (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7558 eq34857
    | (have j0 := eq34857 (σ y)
       grind)
    | exact resolve eq34857 eq7558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7558 eq34857
  have eq35023 : (τ (σ x)) = (k (k y y) (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq34978
  have eq35048 : (τ (σ x)) = (k (k y y) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq35023
       have r₂ := eq17166
       grind)
    | exact resolve eq35023 eq17166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35023
  have eq35075 : (τ (σ x)) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq35048
    | exact resolve eq35048 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq35048
  have eq35090 : x = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq35075
    | exact resolve eq35075 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35075
  have eq35104 : (M.op x y) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq35090
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq35090
    | exact resolve eq35090 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35090
  have eq35127 : (M.op (M.op y y) (M.op x y)) = (k y y) ∨ y = (M.op (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq161 (k y y) y
       have i₂ := eq35104
       grind)
    | exact superpose eq35104 eq161
    | (have j0 := eq161 (k y y) y
       grind)
    | exact resolve eq161 eq35104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq35129 : x = (k y y) ∨ y = (M.op (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37 eq35127
    | exact resolve eq35127 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq35127
  have eq35133 : y = (M.op (k y y) y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq35129
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq35129
    | exact resolve eq35129 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079 eq35129
  have eq74565 : y ≠ y ∨ y = (M.op y y) ∨ (k y y) = (k (k y y) y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (k y y) y
       have i₂ := eq35133
       grind)
    | exact superpose eq35133 eq12
    | (have j0 := eq12 (k y y) y
       grind)
    | (have r₁ := eq12 (k y y) y
       have r₂ := eq35133
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq35133
       grind)
    | exact resolve eq12 eq35133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35133
  have eq74575 : y = (M.op y y) ∨ (k y y) = (k (k y y) y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq74565
  have eq74580 : y = (M.op y y) ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq35104 eq74575
    | exact resolve eq74575 eq35104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35104 eq74575
  have eq74581 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq74580
  have eq75913 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq74581 eq36
    | exact resolve eq36 eq74581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq74581
  have eq75924 : (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17158 eq75913
    | exact resolve eq75913 eq17158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17158 eq75913
  have eq75961 : (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq75924
       have r₂ := eq17166
       grind)
    | exact resolve eq75924 eq17166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75924
  have eq75974 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3761
       have i₂ := eq75961
       grind)
    | exact superpose eq75961 eq3761
    | exact resolve eq3761 eq75961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761
  have eq76005 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2139 y y
       have i₂ := eq75961
       grind)
    | exact superpose eq75961 eq2139
    | (have j0 := eq2139 y y
       grind)
    | exact resolve eq2139 eq75961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139 eq75961
  have eq76010 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq76005
  have eq76027 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq75974
  have eq76042 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3083 eq76027
    | exact resolve eq76027 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083 eq76027
  have eq76057 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq76010 eq76042
    | exact resolve eq76042 eq76010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76010 eq76042
  have eq76058 : y = (M.op y y) := by grind
  clear eq76057
  have eq76078 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq76058
       grind)
    | exact superpose eq76058 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq76058
       grind)
    | exact resolve eq13 eq76058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76145 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq76078 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76078
  have eq76463 : y = (k y y) := by
    first
    | (have i₁ := eq76058
       have i₂ := eq76145 y
       grind)
    | exact superpose eq76145 eq76058
    | exact resolve eq76058 eq76145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76058
  have eq76464 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq3081
       have i₂ := eq76145 sF0
       grind)
    | exact superpose eq76145 eq3081
    | exact resolve eq3081 eq76145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081 eq76145
  have eq76668 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq798 y X0
       have i₂ := eq76463
       grind)
    | exact superpose eq76463 eq798
    | (have j0 := eq798 y X0
       grind)
    | exact resolve eq798 eq76463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq76681 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq543 y y
       have i₂ := eq76463
       grind)
    | exact superpose eq76463 eq543
    | (have j0 := eq543 y y
       grind)
    | exact resolve eq543 eq76463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq76463
  have eq76688 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq76681
  have eq76691 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq76668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76668
  have eq76696 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76688
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76688
    | exact resolve eq76688 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76688
  have eq76698 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq76691 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76691
    | (have j0 := eq76691 X0
       grind)
    | exact resolve eq76691 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76691
  have eq76724 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq76464 eq53
    | exact resolve eq53 eq76464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq76730 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq76464 eq2308
    | (have j0 := eq2308 (M.op x y) y
       grind)
    | exact resolve eq2308 eq76464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308 eq76464
  have eq76735 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq76730
    | exact resolve eq76730 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76730
  have eq76738 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq76724
    | exact resolve eq76724 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76724
  have eq76745 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3090 eq76735
    | exact resolve eq76735 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76735
  have eq76747 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq76738
    | exact resolve eq76738 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76738
  have eq76752 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq76745
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76745
    | exact resolve eq76745 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76745
  have eq76756 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17159 eq76752
    | exact resolve eq76752 eq17159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17159 eq76752
  have eq76757 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq76696 eq76756
    | exact resolve eq76756 eq76696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76696 eq76756
  have eq76758 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq76757
       have r₂ := eq17166
       grind)
    | exact resolve eq76757 eq17166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76757
  have eq76759 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq76758
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76758
    | exact resolve eq76758 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq76758
  have eq76760 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq76698 eq76759
    | exact resolve eq76759 eq76698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76698 eq76759
  have eq76761 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq76760
    | exact resolve eq76760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq76760
  have eq76762 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3090 eq76761
    | exact resolve eq76761 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090 eq76761
  have eq76763 : (σ x) = (σ y) := by
    first
    | exact superpose eq76747 eq76762
    | exact resolve eq76762 eq76747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76747 eq76762
  have eq76764 : False := by grind
  exact eq76764
